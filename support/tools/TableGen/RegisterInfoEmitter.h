//===- RegisterInfoEmitter.h - Generate a Register File Desc. ---*- C++ -*-===//
//
// This tablegen backend is responsible for emitting a description of a target
// register file for a code generator.  It uses instances of the Register,
// RegisterAliases, and RegisterClass classes to gather this information.
//
//===----------------------------------------------------------------------===//

#ifndef REGISTER_INFO_EMITTER_H
#define REGISTER_INFO_EMITTER_H

#include <iosfwd>
class RecordKeeper;

class RegisterInfoEmitter {
  RecordKeeper &Records;
public:
  RegisterInfoEmitter(RecordKeeper &R) : Records(R) {}
  
  // run - Output the register file description, returning true on failure.
  void run(std::ostream &o);

  // runHeader - Emit a header fragment for the register info emitter.
  void runHeader(std::ostream &o);
private:
};

#endif
