//===- BlackfinISelLowering.h - Blackfin DAG Lowering Interface -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the interfaces that Blackfin uses to lower LLVM code into a
// selection DAG.
//
//===----------------------------------------------------------------------===//

#ifndef BLACKFIN_ISELLOWERING_H
#define BLACKFIN_ISELLOWERING_H

#include "llvm/Target/TargetLowering.h"
#include "Blackfin.h"

namespace llvm {

  namespace BFISD {
    enum {
      FIRST_NUMBER = ISD::BUILTIN_OP_END,
      CALL,                     // A call instruction.
      RET_FLAG,                 // Return with a flag operand.
      Wrapper                   // Address wrapper
    };
  }

  class BlackfinTargetLowering : public TargetLowering {
    int VarArgsFrameOffset;   // Frame offset to start of varargs area.
  public:
    BlackfinTargetLowering(TargetMachine &TM);
    virtual MVT getSetCCResultType(MVT VT) const;
    virtual SDValue LowerOperation(SDValue Op, SelectionDAG &DAG);

    int getVarArgsFrameOffset() const { return VarArgsFrameOffset; }

    ConstraintType getConstraintType(const std::string &Constraint) const;
    std::pair<unsigned, const TargetRegisterClass*>
    getRegForInlineAsmConstraint(const std::string &Constraint, MVT VT) const;
    std::vector<unsigned>
    getRegClassForInlineAsmConstraint(const std::string &Constraint,
                                      MVT VT) const;
    virtual bool isOffsetFoldingLegal(const GlobalAddressSDNode *GA) const;
    const char *getTargetNodeName(unsigned Opcode) const;
    unsigned getFunctionAlignment(const Function *F) const;

  private:
    SDValue LowerGlobalAddress(SDValue Op, SelectionDAG &DAG);
    SDValue LowerJumpTable(SDValue Op, SelectionDAG &DAG);
    SDValue LowerFORMAL_ARGUMENTS(SDValue Op, SelectionDAG &DAG);
    SDValue LowerRET(SDValue Op, SelectionDAG &DAG);
    SDValue LowerCALL(SDValue Op, SelectionDAG &DAG);
    SDValue LowerADDE(SDValue Op, SelectionDAG &DAG);
  };
} // end namespace llvm

#endif    // BLACKFIN_ISELLOWERING_H
