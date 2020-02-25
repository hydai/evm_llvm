//===- EVMStackStatus --------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_EVM_EVMSTACKSTATUS_H
#define LLVM_LIB_TARGET_EVM_EVMSTACKSTATUS_H

#include "llvm/ADT/DenseMap.h"

#include <vector>

namespace llvm {
namespace evm {

class StackStatus {
public:
  StackStatus() {}

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

  llvm::DenseMap<unsigned, unsigned> remainingUses;
};

};
};


#endif