
#include "EVMStackStatus.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/Support/Debug.h"

#define DEBUG_TYPE "evm-stackstatus"

using namespace llvm;

namespace evm {

unsigned EVMStackStatus::getStackDepth() const {
  return stackElements.size();
}

unsigned EVMStackStatus::get(unsigned depth) const {
  return stackElements.rbegin()[depth];
}

void EVMStackStatus::swap(unsigned depth) {
    assert(depth != 0);
    assert(stackElements.size() >= 2);
    /*
    LLVM_DEBUG({
      unsigned first = stackElements.rbegin()[0];
      unsigned second = stackElements.rbegin()[depth];
      unsigned fst_idx = Register::virtReg2Index(first);
      unsigned snd_idx = Register::virtReg2Index(second);
      dbgs() << "  SWAP" << depth << ": Swapping %" << fst_idx << " and %"
             << snd_idx << "\n";
    });
    */
    std::iter_swap(stackElements.rbegin(), stackElements.rbegin() + depth);
}

void EVMStackStatus::dup(unsigned depth) {
  unsigned elem = *(stackElements.rbegin() + depth);

  /*
  LLVM_DEBUG({
    unsigned idx = Register::virtReg2Index(elem);
    dbgs() << "  Duplicating " << idx << " at depth " << depth << "\n";
  });
  */

  stackElements.push_back(elem);
}

void EVMStackStatus::pop() {
  /*
  LLVM_DEBUG({
    unsigned reg = stackElements.back();
    unsigned idx = Register::virtReg2Index(reg);
    dbgs() << "  Popping %" << idx << " from stack.\n";
  });
  stackElements.pop_back();
  */
}

void EVMStackStatus::push(unsigned reg) {
  /*
  LLVM_DEBUG({
    unsigned idx = Register::virtReg2Index(reg);
    dbgs() << "  Pushing %" << idx << " to top of stack.\n";
  });
  */
  stackElements.push_back(reg);
}


void EVMStackStatus::dump() const {
  /*
  LLVM_DEBUG({
    dbgs() << "  Stack :  xRegion_size = " << getSizeOfXRegion() << "\n";
    unsigned counter = 0;
    for (auto i = stackElements.rbegin(), e = stackElements.rend(); i != e; ++i) {
      unsigned idx = Register::virtReg2Index(*i);
      dbgs() << "(" << counter << ", %" << idx << "), ";
      counter ++;
    }
    dbgs() << "\n";
  });
  */
}

unsigned EVMStackStatus::findRegDepth(unsigned reg) const {
  unsigned curHeight = getStackDepth();

  for (unsigned d = 0; d < curHeight; ++d) {
    unsigned stackReg = get(d);
    if (stackReg == reg) {
      return d;
      /*
      depth = d;
      LLVM_DEBUG({
        dbgs() << "  Found %" << Register::virtReg2Index(reg)
               << " at depth: " << depth << "\n";
      });
      return depth;
      */
    }
  }
  llvm_unreachable("Cannot find register on stack");
}
};