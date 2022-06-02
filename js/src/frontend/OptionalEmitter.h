/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef frontend_OptionalEmitter_h
#define frontend_OptionalEmitter_h

#include "mozilla/Attributes.h"
#include "frontend/BytecodeControlStructures.h" // BreakableControl
#include "frontend/IfEmitter.h"  // IfEmitter, InternalIfEmitter, CondEmitter
#include "frontend/TDZCheckCache.h"

namespace js {
namespace frontend {

struct BytecodeEmitter;

class MOZ_RAII OptionalEmitter {
  public:
    enum class Kind {
        // Requires two values on the stack
        Reference,
        // Requires one value on the stack
        Other
    };

  private:
    BytecodeEmitter* bce_;

    TDZCheckCache tdzCache_;

    // jumpTarget for the fake label over the optional chaining code
    JumpList top_;

    // BreakableControl target for the break from inside the optional chaining code
    BreakableControl breakInfo_;

    int32_t initialDepth_;

    // JSOp is the op code to be emitted, Kind is if we are dealing with a
    // reference (in which case we need two elements on the stack) or other value
    // (which needs one element on the stack)
    JSOp op_;
    Kind kind_;

  public:
    OptionalEmitter(BytecodeEmitter* bce, int32_t initialDepth,
                    JSOp op = JSOP_UNDEFINED, Kind kind = Kind::Other);

    MOZ_MUST_USE bool emitOptionalJumpLabel();
    MOZ_MUST_USE bool emitJumpShortCircuit();
    MOZ_MUST_USE bool emitJumpShortCircuitForCall();
    MOZ_MUST_USE bool emitOptionalJumpTarget();
};

} /* namespace frontend */
} /* namespace js */

#endif /* frontend_OptionalEmitter_h */
