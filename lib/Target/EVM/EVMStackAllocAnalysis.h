//===- EVMStackAllocAnalysis --------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_EVM_EVMSTACKALLOCANALYSIS_H
#define LLVM_LIB_TARGET_EVM_EVMSTACKALLOCANALYSIS_H

#include "EVM.h"
#include "EVMTargetMachine.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Triple.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/CodeGen/LiveIntervals.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"

#include <algorithm>
#include <memory>

namespace llvm {

typedef enum {
  NONSTACK      = 0x00,  // allocate on memory
  X_STACK       = 0x01,  // transfer
  L_STACK       = 0x02,  // local
  NO_ALLOCATION = 0x04,  // do not allocate
} StackRegion;

// We also assign a memory slot
typedef struct StackAssignment_ {
  StackRegion region;
  // For memory allocation
  unsigned slot;
} StackAssignment;

// The stack arrangement is as follows:
// 
// +----------------+
// |                |
// |  Locals        |
// |                |
// +----------------+
// |                |
// |  Transfers     |
// |                |
// +----------------+
// 
// So we can calculate an element's depth.

// This class records basic block edge set information.
class EdgeSets {
public:
  typedef std::pair<MachineBasicBlock *, MachineBasicBlock *> Edge;
  void computeEdgeSets(MachineFunction *MF);
  unsigned getEdgeSetIndex(Edge edge) const;
  unsigned getEdgeIndex(Edge edge) const;

  Edge getEdge(unsigned edgeIndex) const;
  unsigned getEdgeSet(unsigned edgesetIndex) const;

  void reset() {
    edgeIndex2EdgeSet.clear();
    edgeIndex.clear();
  }

  void dump() const;

private:
  // Index :: EdgeSet
  std::map<unsigned, unsigned> edgeIndex2EdgeSet;   

  // Index : Edge
  std::map<unsigned, Edge> edgeIndex;

  void collectEdges(MachineFunction *MF);

  // given two edges, merge their edgesets.
  void mergeEdgeSets(Edge edge1, Edge edge2);

};

class EVMStackStatus {
public:
  EVMStackStatus() {}

  void swap(unsigned depth);
  void dup(unsigned depth);
  void push(unsigned reg);
  void pop();

  unsigned get(unsigned depth) const;
  void dump() const;

  unsigned getSizeOfXRegion() const {
    return sizeOfXRegion;
  }
  unsigned getSizeOfLRegion() const {
    return getStackDepth() - sizeOfXRegion;
  }

  bool empty() const {
    return stackElements.empty();
  }

  void clear() {
    stackElements.clear();
    sizeOfXRegion = 0;
  }

  const std::vector<unsigned> &getStackElements() const {
    return stackElements;
  }

  unsigned findRegDepth(unsigned reg) const;

  // Stack depth = size of X + size of L
  unsigned getStackDepth() const;

  void instantiateXRegionStack(std::vector<unsigned> &stack) {
    assert(getStackDepth() == 0);
    for (auto element : stack) {
      stackElements.push_back(element);
    }
    sizeOfXRegion = stack.size();
  }

private:
  // stack arrangements.
  std::vector<unsigned> stackElements;

  unsigned sizeOfXRegion;
};

class EVMStackAlloc : public MachineFunctionPass {
public:
  static char ID;

  // TODO: 15 is a bit arbitrary:
  static const unsigned MAXIMUM_STACK_DEPTH = 15;

  EVMStackAlloc() : MachineFunctionPass(ID) {
    initializeEVMStackAllocPass(*PassRegistry::getPassRegistry());
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  void allocateRegistersToStack(MachineFunction &F);

  StackAssignment getStackAssignment(unsigned reg) const;

  unsigned getNumOfAllocatedMemorySlots() const {
    return memoryAssignment.size();
  };

  void getXStackRegion(unsigned edgeSetIndex,
                       std::vector<unsigned> xRegion) const;
  
private:
  typedef struct {
    std::set<unsigned> X; // Transfer Stack
    std::set<unsigned> L; // Local Stack
    std::set<unsigned> M; // Memory
    void reset() {
      X.clear();
      L.clear();
      M.clear();
    }
  } StackStatus;

  LiveIntervals *LIS;
  const EVMInstrInfo *TII;
  MachineFunction *F;
  MachineRegisterInfo *MRI;

  // edge set information
  EdgeSets edgeSets;

  // record assignments of each virtual register 
  DenseMap<unsigned, StackAssignment> regAssignments;
  StackStatus currentStackStatus;

  // This is used to find stack locations
  EVMStackStatus stack;

  std::vector<unsigned> memoryAssignment;

  // map: edgeset -> Stack Assignment
  std::map<unsigned, std::vector<unsigned>> edgeset2assignment;

  void initialize();

  // 
  void consolidateXRegionForEdgeSet(unsigned edgeSet);

  // the pass to analyze a single basicblock
  void analyzeBasicBlock(MachineBasicBlock *MBB);

  void handleDef(MachineInstr &MI);
  void handleUses(MachineInstr &MI);

  // handle a single use in the specific machine instruction. 
  void handleSingleUse(MachineInstr &MI, const MachineOperand &MOP);

  // if the def and use is within a single BB
  bool defIsLocal(const MachineInstr &MI) const;

  // return true if the use in the specific MI is the last use of a reg
  bool regIsLastUse(const MachineOperand &MOP) const;

  // return numbers of uses of a register.
  unsigned getRegNumUses(unsigned reg) const;

  // helper function:
  void assignRegister(unsigned reg, StackRegion region);
  void removeRegisterAssignment(unsigned reg, StackRegion region);

  // for allocating 
  unsigned allocateMemorySlot(unsigned reg);
  void deallocateMemorySlot(unsigned reg);

  unsigned allocateXRegion(unsigned setIndex, unsigned reg);

  bool hasUsesAfterInSameBB(unsigned reg, const MachineInstr &MI) const;
  bool successorsHaveUses(unsigned useReg, const MachineInstr &MI) const;

  // test if we should spill some registers to memory
  unsigned getCurrentStackDepth() const; 

  void pruneStackDepth();
  unsigned findSpillingCandidate(std::set<unsigned> &vecRegs) const;

  bool liveIntervalWithinSameEdgeSet(unsigned def);


  void beginOfBlockUpdates(MachineBasicBlock *MBB);
  void endOfBlockUpdates(MachineBasicBlock* MBB);

  // Stack manipulation operations
  void insertLoadFromMemoryBefore(unsigned reg, MachineInstr &MI, unsigned memSlot);
  void insertStoreToMemoryAfter(unsigned reg, MachineInstr &MI, unsigned memSlot);
  void insertDupBefore(unsigned index, MachineInstr &MI);
  void insertSwapBefore(unsigned index, MachineInstr &MI);
  void insertPopAfter(MachineInstr &MI);


  bool runOnMachineFunction(MachineFunction &MF) override;
};

} // end namespace llvm

#endif // LLVM_LIB_TARGET_EVM_EVMSTACKALLOCANALYSIS_H
