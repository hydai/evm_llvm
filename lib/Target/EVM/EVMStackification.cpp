//===-- EVMStackification.cpp - Optimize stack operands ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file Ported over from WebAssembly backend.
///
//===----------------------------------------------------------------------===//

#include "EVM.h"
#include "EVMMachineFunctionInfo.h"
#include "EVMSubtarget.h"
#include "EVMRegisterInfo.h"
#include "EVMTargetMachine.h"
#include "EVMStackStatus.h"
#include "EVMStackAllocAnalysis.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineDominanceFrontier.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/LiveIntervals.h"

using namespace llvm;

#define DEBUG_TYPE "evm-stackification"

namespace {

class EVMStackification final : public MachineFunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  EVMStackification() : MachineFunctionPass(ID) {}

  StringRef getPassName() const override { return "EVM Stackification"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<LiveIntervals>();
    AU.addRequired<MachineDominatorTree>();
    AU.addRequired<MachineDominanceFrontier>();
    AU.addRequired<EVMStackAlloc>();
    AU.addPreserved<MachineDominatorTree>();
    MachineFunctionPass::getAnalysisUsage(AU);
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

private:
  bool isSingleDefSingleUse(unsigned RegNo) const;
  MachineInstr *getVRegDef(unsigned Reg, const MachineInstr *Insert) const;

  void handleUses(evm::StackStatus &ss, MachineInstr &MI);
  void handleDef(evm::StackStatus &ss, MachineInstr &MI);

  void handle2Uses(evm::StackStatus &ss, MachineInstr &MI);

  // last use: first, second 
  void handle2UsesYY(evm::StackStatus &ss, MachineInstr &MI);
  void handle2UsesYN(evm::StackStatus &ss, MachineInstr &MI);
  void handle2UsesNY(evm::StackStatus &ss, MachineInstr &MI);
  void handle2UsesNN(evm::StackStatus &ss, MachineInstr &MI);

  bool canStackifyReg(unsigned reg, MachineInstr &MI) const;
  unsigned findNumOfUses(unsigned reg) const;

  void insertPop(MachineInstr &MI, evm::StackStatus& ss);
  void insertDupBefore(unsigned index, MachineInstr &MI, evm::StackStatus &ss);
  void insertSwapBefore(unsigned index, MachineInstr &MI, evm::StackStatus &ss);

  void insertLoadFromMemoryBefore(unsigned reg, MachineInstr& MI);
  void insertLoadFromMemoryBefore(unsigned reg, MachineInstr& MI, unsigned memSlot);
  void insertStoreToMemory(unsigned reg, MachineInstr &MI, bool insertAfter);
  void insertStoreToMemoryAfter(unsigned reg, MachineInstr &MI, unsigned memSlot);

  void bringOperandToTop(evm::StackStatus &ss, unsigned depth, MachineInstr &MI);

  void handleIrregularInstruction(evm::StackStatus &ss, MachineInstr &MI);

  void handleEntryMBB(evm::StackStatus &ss, MachineBasicBlock &MBB);
  void handleMBB(MachineBasicBlock &MBB);

  EVMStackAlloc *getStackAllocAnalysis();
  bool isLastUse(MachineOperand &MO) const;

  void reconstructStackStatus(evm::StackStatus &ss, MachineBasicBlock &MBB);

  DenseMap<unsigned, unsigned> reg2index;

  const EVMInstrInfo *TII;
  MachineRegisterInfo *MRI;
  LiveIntervals *LIS;
  EVMMachineFunctionInfo *MFI;
  EVMStackAlloc *ESA;
};
} // end anonymous namespace

char EVMStackification::ID = 0;
INITIALIZE_PASS(EVMStackification, DEBUG_TYPE,
      "Converting register-based instructions into stack instructions",
      false, false)

FunctionPass *llvm::createEVMStackification() {
  return new EVMStackification();
}

bool EVMStackification::isSingleDefSingleUse(unsigned RegNo) const {
  return (MRI->hasOneUse(RegNo) && MRI->hasOneDef(RegNo));
}

// Identify the definition for this register at this point. This is a
// generalization of MachineRegisterInfo::getUniqueVRegDef that uses
// LiveIntervals to handle complex cases.
MachineInstr *EVMStackification::getVRegDef(unsigned Reg,
                                            const MachineInstr *Insert) const {
  // Most registers are in SSA form here so we try a quick MRI query first.
  if (MachineInstr *Def = MRI->getUniqueVRegDef(Reg))
    return Def;

  auto &LIS = *this->LIS;

  // MRI doesn't know what the Def is. Try asking LIS.
  if (const VNInfo *ValNo = LIS.getInterval(Reg).getVNInfoBefore(
          LIS.getInstructionIndex(*Insert)))
    return LIS.getInstructionFromIndex(ValNo->def);

  return nullptr;
}

/***
// The following are the criteria for deciding whether to stackify the register
// or not:
// 1. This reg has only one def
// 2. the uses of the reg is in the same basicblock
*/
bool EVMStackification::canStackifyReg(unsigned reg, MachineInstr& MI) const {
  assert(!Register::isPhysicalRegister(reg));

  const LiveInterval &LI = LIS->getInterval(reg);
  
  // if it has multiple VNs, ignore it.
  if (LI.segments.size() > 1) {
    return false;
  }

  // if it goes across multiple MBBs, ignore it.
  MachineBasicBlock* MBB = MI.getParent();
  SlotIndex MBBBegin = LIS->getMBBStartIdx(MBB);
  SlotIndex MBBEnd = LIS->getMBBEndIdx(MBB);

  if(!LI.isLocal(MBBBegin, MBBEnd)) {
    return false;
  }

  return true;
}

unsigned EVMStackification::findNumOfUses(unsigned reg) const {
  auto useOperands = MRI->reg_nodbg_operands(reg);
  unsigned numUses = std::distance(useOperands.begin(), useOperands.end());
  return numUses;
}

void EVMStackification::insertPop(MachineInstr &MI, evm::StackStatus &ss) {
  MachineBasicBlock *MBB = MI.getParent();
  MachineFunction &MF = *MBB->getParent();
  MachineInstrBuilder pop = BuildMI(MF, MI.getDebugLoc(), TII->get(EVM::POP_r));
  MBB->insertAfter(MachineBasicBlock::iterator(MI), pop);

  ss.pop();
}

void EVMStackification::insertDupBefore(unsigned index, MachineInstr &MI, evm::StackStatus &ss) {
  MachineBasicBlock *MBB = MI.getParent();
  MachineFunction &MF = *MBB->getParent();
  MachineInstrBuilder dup = BuildMI(MF, MI.getDebugLoc(), TII->get(EVM::DUP_r)).addImm(index);
  MBB->insert(MachineBasicBlock::iterator(MI), dup);
  ss.dup(index);
}

// The skip here means how many same items needs to be skipped.
static unsigned findRegDepthOnStack(evm::StackStatus &ss, unsigned reg) {
  unsigned curHeight = ss.getStackDepth();
  unsigned depth = 0;

  for (unsigned d = 0; d < curHeight; ++d) {
    unsigned stackReg = ss.get(d);
    if (stackReg == reg) {
        depth = d;
        LLVM_DEBUG({
          dbgs() << "  Found %" << Register::virtReg2Index(reg)
                 << " at depth: " << depth << "\n";
        });
        return depth;
    }
  }
  llvm_unreachable("Cannot find register on stack");
}

void EVMStackification::insertSwapBefore(unsigned index, MachineInstr &MI,
                                         evm::StackStatus &ss) {
  MachineBasicBlock *MBB = MI.getParent();
  MachineInstrBuilder swap =
      BuildMI(*MBB->getParent(), MI.getDebugLoc(), TII->get(EVM::SWAP_r))
          .addImm(index);
  MBB->insert(MachineBasicBlock::iterator(MI), swap);
  ss.swap(index);
}

void EVMStackification::insertLoadFromMemoryBefore(unsigned reg,
                                                   MachineInstr &MI,
                                                   unsigned memSlot) {
  LLVM_DEBUG(dbgs() << "  %" << Register::virtReg2Index(reg) << " <= GETLOCAL("
                    << index << ") inserted.\n");

  BuildMI(*MI.getParent(), MI, MI.getDebugLoc(), TII->get(EVM::pGETLOCAL_r), reg)
      .addImm(memSlot);
}

void EVMStackification::insertStoreToMemoryAfter(unsigned reg, MachineInstr &MI, unsigned memSlot) {
  MachineBasicBlock *MBB = MI.getParent();
  MachineFunction &MF = *MBB->getParent();

  MachineInstrBuilder putlocal =
      BuildMI(MF, MI.getDebugLoc(), TII->get(EVM::pPUTLOCAL_r)).addReg(reg).addImm(memSlot);
  MBB->insertAfter(MachineBasicBlock::iterator(MI), putlocal);
  LLVM_DEBUG(dbgs() << "  PUTLOCAL(" << index << ") => %" << memSlot << 
                 "  is inserted.\n");
}

void EVMStackification::insertStoreToMemory(unsigned reg, MachineInstr &MI, bool InsertAfter = true) {
  MachineBasicBlock *MBB = MI.getParent();
  MachineFunction &MF = *MBB->getParent();

  unsigned index = MFI->get_memory_index(reg);
  unsigned ridx = Register::virtReg2Index(reg);
  LLVM_DEBUG(dbgs() << "  PUTLOCAL(" << index << ") => %" << ridx << 
                 "  is inserted.\n");
  MachineInstrBuilder putlocal =
      BuildMI(MF, MI.getDebugLoc(), TII->get(EVM::pPUTLOCAL_r)).addReg(reg).addImm(index);
  if (InsertAfter) {
    MBB->insertAfter(MachineBasicBlock::iterator(MI), putlocal);
  } else {
    MBB->insert(MachineBasicBlock::iterator(MI), putlocal);
  }
}

// bring a stack element to top, without altering other stack element positions.
void EVMStackification::bringOperandToTop(evm::StackStatus &ss, unsigned depth,
                                          MachineInstr &MI) {
  assert(depth <= 16);

  for (unsigned i = 1; i <= depth; ++i) {
    insertSwapBefore(i, MI, ss);
    ss.swap(i);
  }
}

void EVMStackification::handleIrregularInstruction(evm::StackStatus &ss,
                                                   MachineInstr &MI) {
  // iterate over the operands (back to front), and bring each of them to top.
  unsigned use_counter = MI.getNumOperands() - 1;
  unsigned end_defs = MI.getNumExplicitDefs() - 1;

  unsigned pop_counter = 0;
  while (use_counter != end_defs) {
    const MachineOperand &MO = MI.getOperand(use_counter);
    --use_counter;
    ++pop_counter;

    if (!MO.isReg() || MO.isImplicit()) {
      LLVM_DEBUG(dbgs() << "  Operand is not reg or is implicit, skip: ";
                 MO.dump());
      return;
    }

    unsigned reg = MO.getReg();
    if (!MFI->isVRegStackified(reg)) {
      LLVM_DEBUG(dbgs() << "  Operand is not stackified: "; MO.dump());
      insertLoadFromMemoryBefore(reg, MI);
      ss.push(reg);
    } else {
      LLVM_DEBUG(dbgs() << "  Operand is stackified: "; MO.dump());
      // stackified case:
      unsigned depthFromTop = findRegDepthOnStack(ss, reg);

      bringOperandToTop(ss, depthFromTop, MI);
    }
  }

  for (unsigned i = 0; i < MI.getNumOperands() - MI.getNumExplicitDefs(); ++i) {
    ss.pop();
  }

}

bool EVMStackification::isLastUse(MachineOperand &MO) const {
  assert(MO.isReg() && "Operand my be a register");
  unsigned useReg = MO.getReg();

  // unfortunately, the <kill> flag is conservative, when <kill> is set, it is
  // true. so we have to do some other tricks to make sure we do not miss killed
  // registers.
  if (MO.isKill()) {
    return true;
  }

  MachineInstr *MI = MO.getParent();
  MachineBasicBlock* MBB = MI->getParent();
  const LiveInterval &LI = LIS->getInterval(useReg);

  // It is not the last use in current MBB:
  SlotIndex MBBEndIndex = LIS->getMBBEndIdx(MBB);
  SlotIndex regSI = LIS->getInstructionIndex(*MI);

  // 
  if (LI.find(regSI) != LI.end()) {
    
  }

  // If it is the last use of this MBB, then make sure:
  // Jumping out of MBB will go out of liveness scope .
  for (MachineBasicBlock *NextMBB : MBB->successors()) {
    SlotIndex NextMBBBeginIndex = LIS->getMBBStartIdx(NextMBB);
    if (LI.liveAt(NextMBBBeginIndex)) {
      return false;
    }
  }

  return true;
}

void EVMStackification::handle2Uses(evm::StackStatus &ss, MachineInstr& MI) {

}

void EVMStackification::handleUses(evm::StackStatus &ss, MachineInstr& MI) {

  // calculate number of register uses
  unsigned numUsesInMI = 0;
  for (MachineOperand &MO : MI.uses()) {
    if (MO.isReg()) {
      ++numUsesInMI;
    }
  }

  if (numUsesInMI == 1) {
    // get first operand
    MachineOperand &MO = *MI.uses().begin();
    unsigned useReg = MO.getReg();
    StackAssignment sa = ESA->getStackAssignment(useReg);

    switch (sa.region) {
      default: {
        llvm_unreachable("Impossible switch.");
        break;
      }
      case X_STACK:
      case L_STACK: {
        // it is fairly straightforward for the case of only use consuming
        // operand
        unsigned depth = findRegDepthOnStack(ss, useReg);
        if (depth != 0) {
          if (isLastUse(MO)) {
            insertSwapBefore(depth, MI, ss);
          } else {
            insertDupBefore(depth, MI, ss);
          }
        }
        break;
      }
      case NONSTACK: {
        unsigned slot = sa.memorySlot;
        insertLoadFromMemoryBefore(useReg, MI, slot);
        break;
      }
    }
    return;
  }

  if (numUsesInMI == 2) {
    MachineOperand &MO1 = *MI.uses().begin();
    MachineOperand &MO2 = *(MI.uses().begin() + 1);

    assert(MO1.isReg() && MO2.isReg());

    unsigned firstReg  = MO1.getReg();
    unsigned secondReg = MO2.getReg();
    StackAssignment fa = ESA->getStackAssignment(firstReg);
    StackAssignment sa = ESA->getStackAssignment(secondReg);

    // move the memory allocated variable to stack if needed
    unsigned shouldSwapFirst  = isLastUse(MO1);
    unsigned shouldSwapSecond = isLastUse(MO2);

    if (sa.region == NONSTACK) {
      unsigned slot = sa.memorySlot;
      insertLoadFromMemoryBefore(secondReg, MI, slot);
      shouldSwapFirst = true;
    }

    if (fa.region == NONSTACK) {
      unsigned slot = sa.memorySlot;
      insertLoadFromMemoryBefore(firstReg, MI, slot);
      shouldSwapSecond = true;
    }

    // now check step depth
    unsigned fd = findRegDepthOnStack(ss, firstReg);
    unsigned sd = findRegDepthOnStack(ss, secondReg);

    // shortcut
    if (fd == 0 && sd == 1) {
      return;
    }

    // second is not in place, and is swappable
    if (sd != 1) {
      if (shouldSwapSecond) {
        insertSwapBefore(sd, MI, ss);
      } else {
        // should dup
        insertDupBefore(sd, MI, ss);
      }
      assert(findRegDepthOnStack(ss, firstReg) == 1 && "incompatible results.");
      insertSwapBefore(1, MI, ss);
    }

    // first is not in place, and second is
    if (fd != 0) {
      if (shouldSwapFirst) {
        insertSwapBefore(fd, MI, ss);
      } else {
        // bring second in place first,
        insertSwapBefore(1, MI, ss);
        // then duplicate first.
        insertDupBefore(fd, MI, ss);
      }
    }

    // first and second not in place
  }

  LLVM_DEBUG({
    dbgs() << "  numUsesInMI == " << numUsesInMI << ", handle specifically\n";
  });

  handleIrregularInstruction(ss, MI);
  return;
}

void EVMStackification::handleDef(evm::StackStatus &ss, MachineInstr& MI) {
  unsigned numDefs = MI.getDesc().getNumDefs();
  assert(numDefs <= 1 && "more than one defs");

  // skip if there is no definition.
  if (numDefs == 0) {
    return;
  }

  MachineOperand& def = *MI.defs().begin();
  assert(def.isReg() && def.isDef());
  unsigned defReg = def.getReg();

  StackAssignment sa = ESA->getStackAssignment(defReg);

  // First we push it to stack
  ss.push(defReg);

  switch (sa.region) {
    default:
      llvm_unreachable("Impossible path");
      break;
    case NO_ALLOCATION: {
      assert(MRI->use_empty(defReg));
      insertPop(MI, ss);
      break;
    }
    case X_STACK: {
      unsigned x_slot = sa.stackSlot;
      // we should ensure that the order is the same as the result of
      // analysis
      llvm_unreachable("unimplemented");
      break;
    }
    case L_STACK: {
      llvm_unreachable("unimplemented");
      break;
    }
    case NONSTACK: {
      insertStoreToMemoryAfter(defReg, MI, sa.memorySlot);
      break; 
    }
  }
}

typedef struct {
  unsigned reg;
  bool canStackify;
} Sarg;

void EVMStackification::handleEntryMBB(evm::StackStatus &ss, MachineBasicBlock &MBB) {
    assert(ss.getStackDepth() == 0);

    std::vector<Sarg> canStackifyStackarg;

    LLVM_DEBUG({ dbgs() << "// start of handling stack args.\n"; });
    // iterate over stackargs:
    MachineBasicBlock::iterator SI;
    for (MachineBasicBlock::iterator I = MBB.begin(), E = MBB.end();
         I != E; ++I) {
      MachineInstr &MI = *I;

      if (MI.getOpcode() != EVM::pSTACKARG_r) {
        SI = I;
        break;
      }
      // record stack arg status.
      unsigned reg = MI.getOperand(0).getReg();
      bool canStackfy = canStackifyReg(reg, MI);
      Sarg x{reg, canStackfy};
      canStackifyStackarg.push_back(x);

      LLVM_DEBUG({
        unsigned ridx = Register::virtReg2Index(reg);
        dbgs() << "Stackarg Reg %" << ridx << " is stackifiable? "
               << canStackfy << "\n";
      });

      // we should also update stackstatus:
      ss.push(reg);
      ss.dump();
    }

    // This is the instruction of the first non-stackarg instruction.
    MachineInstr &MI = *SI;
    LLVM_DEBUG({
      dbgs() << "First non-stack arg instruction:";
      MI.dump();
    });

    // from top to bottom.
    std::reverse(canStackifyStackarg.begin(), canStackifyStackarg.end());

    // insert stack manipulation code here.
    for (unsigned index = 0; index < canStackifyStackarg.size();  ++index) {
      Sarg pos = canStackifyStackarg[index];

      unsigned depth = findRegDepthOnStack(ss, pos.reg);

      LLVM_DEBUG({
        unsigned ridx = Register::virtReg2Index(pos.reg);
        dbgs() << "Handling stackarg  %" << ridx << "\n"; 
      });

      if (pos.canStackify) {
        // duplicate on to top of stack.
        unsigned numUses =
            std::distance(MRI->use_begin(pos.reg), MRI->use_end());
        LLVM_DEBUG({ dbgs() << "  Num of uses: " << numUses << "\n"; });

        for (unsigned i = 1; i < numUses; ++i) {
          if (i == 1) {
            insertDupBefore(depth + 1, MI, ss);
            ss.dup(depth); 
          } else {
            // dup the top
            insertDupBefore(1, MI, ss);
            ss.dup(0);
          }
        }

        // stackify the register
        assert(!MFI->isVRegStackified(pos.reg));
        MFI->stackifyVReg(pos.reg);
        ss.dump();
      } else {
        if (depth != 0) {
          // We can't stackify it:
          // SWAP and then store.
          insertSwapBefore(depth, MI, ss);
          ss.swap(depth);
        }

        MFI->allocate_memory_index(pos.reg);
        // we actually need to insert BEFORE
        insertStoreToMemory(pos.reg, MI, false);
        ss.pop();
        ss.dump();
      }
    }

    LLVM_DEBUG({
      dbgs() << "// end of handling stack args, next instr:";
      (*SI).dump();
    });

    for (MachineBasicBlock::iterator I = SI, E = MBB.end();
         I != E;) {
      MachineInstr &MI = *I++;

      LLVM_DEBUG({
        dbgs() << "Stackifying instr: ";
        MI.dump();
      });

      // If the Use is stackified:
      // insert SWAP if necessary
      handleUses(ss, MI);

      // If the Def is able to be stackified:
      // 1. mark VregStackified
     // 2. insert DUP if necessary
      handleDef(ss, MI);

      ss.dump();
    }

}

void EVMStackification::reconstructStackStatus(evm::StackStatus &ss, MachineBasicBlock &MBB) {
  // find the incoming edgeset:

  // For entry block, everything is empty.
  if (MBB.pred_empty()) {
    assert(ss.getStackDepth() == 0);
    return;
  }

  std::vector<unsigned> xRegion;

  EdgeSets::Edge edge = {*MBB.predecessors().begin(), &MBB};
  unsigned ESIndex = ESA->getEdgeSets().getEdgeSetIndex(edge);
  ESA->getXStackRegion(ESIndex, xRegion);

  ss.instantiateXRegionStack(xRegion);

  LLVM_DEBUG(dbgs() << "Stack's X region at beginning of BB: \n";);
  ss.dump();
}

void EVMStackification::handleMBB(MachineBasicBlock &MBB) {
    // Firstly, we have to retrieve/reconstruct the stack status
    evm::StackStatus ss;
    reconstructStackStatus(ss, MBB);

    // The scheduler has already set the sequence for us. We just need to
    // iterate over by order.
    for (MachineBasicBlock::iterator I = MBB.begin(), E = MBB.end();
         I != E;) {
      MachineInstr &MI = *I++;

      LLVM_DEBUG({
        dbgs() << "Stackifying instr: ";
        MI.dump();
      });

      handleUses(ss, MI);
      handleDef(ss, MI);

      ss.dump();
    }
}

bool EVMStackification::runOnMachineFunction(MachineFunction &MF) {
  LLVM_DEBUG({
    dbgs() << "********** Stackification **********\n"
           << "********** Function: " << MF.getName() << '\n';
  });

  for (MachineBasicBlock &MBB : MF) {
    handleMBB(MBB);
  }


  return true;
}
