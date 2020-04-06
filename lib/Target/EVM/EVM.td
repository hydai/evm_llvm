//===-- EVM.td - Describe the EVM Target Machine -------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

include "llvm/Target/Target.td"

//===----------------------------------------------------------------------===//
// EVM subtarget features and instruction predicates.
//===----------------------------------------------------------------------===//

class Proc<string Name, list<SubtargetFeature> Features>
 : Processor<Name, NoItineraries, Features>;


def FeatureSubroutine : SubtargetFeature<"subroutine", "has_subroutines", "true",
                                         "Ethereum Improvement Proposal 2315">;

def : Proc<"generic", [FeatureSubroutine]>;
def : Proc<"EVM15", [FeatureSubroutine]>;

//===----------------------------------------------------------------------===//
// Registers, instruction descriptions.
//===----------------------------------------------------------------------===//

include "EVMRegisterInfo.td"
include "EVMInstrInfo.td"
include "EVMCallingConv.td"

//===----------------------------------------------------------------------===//
// EVM processors supported.
//===----------------------------------------------------------------------===//

def : ProcessorModel<"generic", NoSchedModel, []>;

//===----------------------------------------------------------------------===//
// Define the EVM target.
//===----------------------------------------------------------------------===//

def EVMInstrInfo : InstrInfo {
  let guessInstructionProperties = 0;
}

def EVMAsmParser : AsmParser {
  let ShouldEmitMatchRegisterAltName = 1;
  let AllowDuplicateRegisterNames = 1;
}

def EVMAsmWriter : AsmWriter {
  int PassSubtarget = 1;
}

def EVM : Target {
  let InstructionSet = EVMInstrInfo;
  let AssemblyParsers = [EVMAsmParser];
  let AssemblyWriters = [EVMAsmWriter];
  let AllowRegisterRenaming = 1;
}
