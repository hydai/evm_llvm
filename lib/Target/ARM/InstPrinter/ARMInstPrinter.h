//===-- ARMInstPrinter.h - Convert ARM MCInst to assembly syntax ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This class prints an ARM MCInst to a .s file.
//
//===----------------------------------------------------------------------===//

#ifndef ARMINSTPRINTER_H
#define ARMINSTPRINTER_H

#include "llvm/MC/MCInstPrinter.h"

namespace llvm {
  class MCOperand;

class ARMInstPrinter : public MCInstPrinter {
public:
  ARMInstPrinter(const MCAsmInfo &MAI) : MCInstPrinter(MAI) {}

  virtual void printInst(const MCInst *MI, raw_ostream &O);
  virtual StringRef getOpcodeName(unsigned Opcode) const;

  static const char *getInstructionName(unsigned Opcode);

  // Autogenerated by tblgen.
  void printInstruction(const MCInst *MI, raw_ostream &O);
  static const char *getRegisterName(unsigned RegNo);


  void printOperand(const MCInst *MI, unsigned OpNo, raw_ostream &O,
                    const char *Modifier = 0);

  void printSOImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printSOImm2PartOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);

  void printSORegOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printAddrMode2Operand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printAddrMode2OffsetOperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printAddrMode3Operand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printAddrMode3OffsetOperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printLdStmModeOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O,
                             const char *Modifier = 0);
  void printAddrMode5Operand(const MCInst *MI, unsigned OpNum, raw_ostream &O,
                             const char *Modifier = 0);
  void printAddrMode6Operand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printAddrMode6OffsetOperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printAddrModePCOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O,
                              const char *Modifier = 0);

  void printBitfieldInvMaskImmOperand(const MCInst *MI, unsigned OpNum,
                                      raw_ostream &O);
  void printMemBOption(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printShiftImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);

  void printThumbS4ImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printThumbITMask(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printThumbAddrModeRROperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printThumbAddrModeRI5Operand(const MCInst *MI, unsigned OpNum,
                                    raw_ostream &O, unsigned Scale);
  void printThumbAddrModeS1Operand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printThumbAddrModeS2Operand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printThumbAddrModeS4Operand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);
  void printThumbAddrModeSPOperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);

  void printT2SOOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printAddrModeImm12Operand(const MCInst *MI, unsigned OpNum,
                                 raw_ostream &O);
  void printT2AddrModeImm8Operand(const MCInst *MI, unsigned OpNum,
                                  raw_ostream &O);
  void printT2AddrModeImm8s4Operand(const MCInst *MI, unsigned OpNum,
                                    raw_ostream &O);
  void printT2AddrModeImm8OffsetOperand(const MCInst *MI, unsigned OpNum,
                                        raw_ostream &O);
  void printT2AddrModeImm8s4OffsetOperand(const MCInst *MI, unsigned OpNum,
                                          raw_ostream &O);
  void printT2AddrModeSoRegOperand(const MCInst *MI, unsigned OpNum,
                                   raw_ostream &O);

  void printSetendOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printCPSOptionOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printMSRMaskOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printNegZeroOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printPredicateOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printMandatoryPredicateOperand(const MCInst *MI, unsigned OpNum,
                                      raw_ostream &O);
  void printSBitModifierOperand(const MCInst *MI, unsigned OpNum,
                                raw_ostream &O);
  void printRegisterList(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printCPInstOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O,
                          const char *Modifier);
  // The jump table instructions have custom handling in ARMAsmPrinter
  // to output the jump table. Nothing further is necessary here.
  void printJTBlockOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O) {}
  void printJT2BlockOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O) {}
  void printTBAddrMode(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printNoHashImmediate(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printVFPf32ImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printVFPf64ImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);
  void printNEONModImmOperand(const MCInst *MI, unsigned OpNum, raw_ostream &O);

  void printPCLabel(const MCInst *MI, unsigned OpNum, raw_ostream &O);
};

}

#endif
