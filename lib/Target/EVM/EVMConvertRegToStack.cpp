//===-- EVMConvertRegToStack.cpp - Move virtual regisers to memory location -===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file implements the actual transformation from register based
/// instructions to stack based instruction. It considers the order of the
/// instructions in a basicblock is correct, and it does not change the order.
/// Some stack manipulation instructions are inserted into the code.
/// It has a prerequiste pass: EVMVRegToMem.
///
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/EVMMCTargetDesc.h"
#include "EVM.h"
#include "EVMMachineFunctionInfo.h"
#include "EVMSubtarget.h"
#include "EVMUtils.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define DEBUG_TYPE "evm-reg-to-stacks"

/// Copied from WebAssembly's backend.
namespace {
class EVMConvertRegToStack final : public MachineFunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  EVMConvertRegToStack() : MachineFunctionPass(ID) {}

private:
  StringRef getPassName() const override {
    return "EVM Convert register to stacks";
  }

  const TargetInstrInfo* TII;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    MachineFunctionPass::getAnalysisUsage(AU);
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

  void convertSWAP(MachineInstr* MI) const;
  void convertDUP(MachineInstr* MI) const;
  void convertMOVE(MachineInstr* MI) const;
};
} // end anonymous namespace

char EVMConvertRegToStack::ID = 0;
INITIALIZE_PASS(EVMConvertRegToStack, DEBUG_TYPE,
                "Convert register-based instructions into stack-based",
                false, false)

FunctionPass *llvm::createEVMConvertRegToStack() {
  return new EVMConvertRegToStack();
}

static unsigned getSWAPOpcode(unsigned idx) {
  switch (idx) {
    case 1 : return EVM::SWAP1;
    case 2 : return EVM::SWAP2;
    case 3 : return EVM::SWAP3;
    case 4 : return EVM::SWAP4;
    case 5 : return EVM::SWAP5;
    case 6 : return EVM::SWAP6;
    case 7 : return EVM::SWAP7;
    case 8 : return EVM::SWAP8;
    case 9 : return EVM::SWAP9;
    case 10: return EVM::SWAP10;
    case 11: return EVM::SWAP11;
    case 12: return EVM::SWAP12;
    case 13: return EVM::SWAP13;
    case 14: return EVM::SWAP14;
    case 15: return EVM::SWAP15;
    case 16: return EVM::SWAP16;
    default:
      llvm_unreachable("invalid index");
  }
}

static unsigned getDUPOpcode(unsigned idx) {
  switch (idx) {
    case 1 : return EVM::DUP1;
    case 2 : return EVM::DUP2;
    case 3 : return EVM::DUP3;
    case 4 : return EVM::DUP4;
    case 5 : return EVM::DUP5;
    case 6 : return EVM::DUP6;
    case 7 : return EVM::DUP7;
    case 8 : return EVM::DUP8;
    case 9 : return EVM::DUP9;
    case 10: return EVM::DUP10;
    case 11: return EVM::DUP11;
    case 12: return EVM::DUP12;
    case 13: return EVM::DUP13;
    case 14: return EVM::DUP14;
    case 15: return EVM::DUP15;
    case 16: return EVM::DUP16;
    default:
      llvm_unreachable("invalid index");
  }
}
void EVMConvertRegToStack::convertMOVE(MachineInstr* MI) const {

}

void EVMConvertRegToStack::convertSWAP(MachineInstr* MI) const {
  unsigned swapIdx = MI->getOperand(0).getImm();
  swapIdx = (swapIdx > 16) ? 16 : swapIdx;
  //assert(swapIdx <= 16 && "invalid SWAP");

  unsigned opc = getSWAPOpcode(swapIdx);

  BuildMI(*MI->getParent(), MI, MI->getDebugLoc(), TII->get(opc));
  MI->removeFromParent();
}

void EVMConvertRegToStack::convertDUP(MachineInstr* MI) const {
  unsigned dupIdx = MI->getOperand(0).getImm();
  assert(dupIdx <= 16 && "invalid DUP");

  unsigned opc = getDUPOpcode(dupIdx);

  BuildMI(*MI->getParent(), MI, MI->getDebugLoc(), TII->get(opc));
  MI->removeFromParent();
}

bool EVMConvertRegToStack::runOnMachineFunction(MachineFunction &MF) {
  LLVM_DEBUG({
    dbgs() << "********** Convert register to stack **********\n"
           << "********** Function: " << MF.getName() << '\n';
  });

  TII = MF.getSubtarget<EVMSubtarget>().getInstrInfo();

  for (MachineBasicBlock & MBB : MF) {
    for (MachineBasicBlock::instr_iterator I = MBB.instr_begin(), E = MBB.instr_end(); I != E;) {
      MachineInstr &MI = *I++;

      unsigned opc = MI.getOpcode();

      // Convert irregular reg->stack mapping
      if (opc == EVM::PUSH32_r) {
        assert(MI.getNumOperands() == 2 && "PUSH32_r's number of operands must be 2.");
        if (!MI.getOperand(1).isReg()) {
          BuildMI(MBB, MI, MI.getDebugLoc(), TII->get(EVM::PUSH32)).add(MI.getOperand(1));
        } else {
          BuildMI(MBB, MI, MI.getDebugLoc(), TII->get(EVM::DUP1));
        }
        MI.eraseFromParent();
        continue;
      }

      if (opc == EVM::pSTACKARG_r) {
        MI.RemoveOperand(0);
        MI.setDesc(TII->get(EVM::pSTACKARG));
        continue;
      }

      // expand SWAP
      if (opc == EVM::SWAP_r) {
        convertSWAP(&MI);
        continue;
      }

      if (opc == EVM::DUP_r) {
        convertDUP(&MI);
        continue;
      }

      // MOVE instruction is simply a copy.
      if (opc == EVM::pMOVE_r) {
        MI.removeFromParent();
        continue;
      }

      for (MachineOperand &MO : reverse(MI.uses())) {
        // register value:
        if (MO.isReg()) {
          assert(!Register::isPhysicalRegister(MO.getReg()) &&
                 "There should be no physical registers at this point.");
        }
      }

      // now def and uses are handled. should convert the instruction.
      {
        auto RegOpcode = MI.getOpcode();
        auto StackOpcode = llvm::EVM::getStackOpcode(RegOpcode);

        if (StackOpcode == -1) {
          // special handling for return pseudo, as we will expand
          // it at the finalization pass.
          if (RegOpcode == EVM::pRETURNSUB_r ||
              RegOpcode == EVM::pRETURNSUBVOID_r) {
            if (MF.getSubtarget<EVMSubtarget>().hasSubroutine()) {
              StackOpcode = EVM::RETURNSUB;
            } else {
              StackOpcode = EVM::JUMP;
            }
          }

          else if (RegOpcode == EVM::pJUMPSUB_r || EVM::pJUMPSUBVOID_r) {
            if (MF.getSubtarget<EVMSubtarget>().hasSubroutine()) {
              StackOpcode = EVM::JUMPSUB;
            } else {
              // store FreeMemory Pointer to latest location:

              EVMMachineFunctionInfo *MFI =
                  MF.getInfo<EVMMachineFunctionInfo>();

              // we implicitly allocate a slot at FP[lastIndex+1]:
              unsigned index = MFI->getNumAllocatedIndexInFunction() + 1;

              // store current FP to fp[index]:
              // TODO can optimize this sequence

              // PUSH fpaddr
              // MLOAD  (fp)
              // DUP1 (fp, fp)
              // PUSH index (index, fp, fp)
              // ADD   (fp+index, fp)
              // MSTORE

              // update FP to FP[index + 1]

              // PUSH fpaddr (fpaddr)
              // MLOAD (fp)
              // PUSH (index + 1) * 32     (index+1, fp)
              // ADD   (fp[index+1])
              // PUSH fpaddr   (fpaddr, fp[index+1])
              // MSTORE

              unsigned fpaddr =
                  MF.getSubtarget<EVMSubtarget>().getFreeMemoryPointer();
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH32))
                  .addImm(fpaddr);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::MLOAD));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::DUP1));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH32))
                  .addImm(index * 32);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::ADD));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::MSTORE));

              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH32))
                  .addImm(fpaddr);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::MLOAD));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH32))
                  .addImm((index + 1) * 32);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::ADD));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH32))
                  .addImm(fpaddr);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::MSTORE));

              // here we build the return address, and insert it as the first
              // argument of the function.
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::PUSH1))
                  .addImm(4);
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::GETPC));
              BuildMI(*MI.getParent(), MI, MI.getDebugLoc(),
                      TII->get(EVM::ADD));

              // swap the callee address with the return address
              unsigned uses = std::distance(MI.uses().begin(), MI.uses().end());
              unsigned opc = getSWAPOpcode(uses);
              auto mm =
                  BuildMI(*MI.getParent(), MI, MI.getDebugLoc(), TII->get(opc));
              // setting comment
              mm->setAsmPrinterFlag(
                  EVM::BuildCommentFlags(EVM::SUBROUTINE_BEGIN, 0));
              StackOpcode = EVM::JUMP;

              MachineBasicBlock::iterator MIT(MI);

              // insert JUMPDEST after MI
              const DebugLoc &DL = MI.getDebugLoc();
              MIT = MBB.insertAfter(MIT,
                                    BuildMI(MF, DL, TII->get(EVM::JUMPDEST)));

              // restore free pointer from index
              // PUSH FPAddr  (fpaddr)
              // MLOAD        (fp)
              // PUSH 32      (32, fp)
              // SWAP1        (fp, 32)
              // SUB          (fp-32)
              // MLOAD        (oldFP)
              // PUSH FPAddr  (fpaddr, oldFP)
              // MSTORE

              // PUSH FPAddr  (fpadd,r fp-32)
              // MSTORE

              MIT = MBB.insertAfter(
                  MIT, BuildMI(MF, DL, TII->get(EVM::PUSH32)).addImm(fpaddr));
              MIT = MBB.insertAfter(MIT, BuildMI(MF, DL, TII->get(EVM::MLOAD)));
              MIT = MBB.insertAfter(
                  MIT, BuildMI(MF, DL, TII->get(EVM::PUSH32)).addImm(32));
              MIT = MBB.insertAfter(MIT, BuildMI(MF, DL, TII->get(EVM::SWAP1)));
              MIT = MBB.insertAfter(MIT, BuildMI(MF, DL, TII->get(EVM::SUB)));
              MIT = MBB.insertAfter(MIT, BuildMI(MF, DL, TII->get(EVM::MLOAD)));
              MIT = MBB.insertAfter(
                  MIT, BuildMI(MF, DL, TII->get(EVM::PUSH32)).addImm(fpaddr));
              MIT =
                  MBB.insertAfter(MIT, BuildMI(MF, DL, TII->get(EVM::MSTORE)));
            }
          }
        }
        assert(StackOpcode != -1 && "Failed to convert instruction to stack mode.");

        MI.setDesc(TII->get(StackOpcode));

        // Remove register operands.
        for (unsigned i = 0; i < MI.getNumOperands();) {
          auto &MO = MI.getOperand(i);
          assert(
              MO.isReg() &&
              "By design we should only see register operands at this point");
          MI.RemoveOperand(i);
        }

      }
    }
  }


  return true;
}
