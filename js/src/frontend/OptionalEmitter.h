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

// Class for emitting bytecode for optional expressions.
//
// Usage: (check for the return value is omitted for simplicity)
//
//   `obj?.prop;`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     PropOpEmitter poe(this,
//                       PropOpEmitter::Kind::Get,
//                       PropOpEmitter::ObjKind::Other);
//     oe.emitOptionalJumpLabel();
//     poe.prepareForObj();
//     emit(obj);
//     oe.emitJumpShortCircuit();
//     poe.emitGet(atom_of_prop);
//     oe.emitOptionalJumpTarget();
//
//   `delete obj?.prop;`
//     OptionalEmitter oe(this, JSOp:True);
//     OptionalPropOpEmitter poe(this,
//                       PropOpEmitter::Kind::Delete,
//                       PropOpEmitter::ObjKind::Other);
//     oe.emitOptionalJumpLabel();
//     poe.prepareForObj();
//     emit(obj);
//     oe.emitJumpShortCircuit();
//     poe.emitDelete(atom_of_prop);
//     oe.emitOptionalJumpTarget();
//
//   `obj?.[key];`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     ElemOpEmitter eoe(this,
//                       ElemOpEmitter::Kind::Get,
//                       ElemOpEmitter::ObjKind::Other);
//     oe.emitOptionalJumpLabel();
//     eoe.prepareForObj();
//     emit(obj);
//     oe.emitJumpShortCircuit();
//     eoe.prepareForKey();
//     emit(key);
//     eoe.emitGet();
//     oe.emitOptionalJumpTarget();
//
//   `delete obj?.[key];`
//     OptionalEmitter oe(this, JSOp::True);
//     ElemOpEmitter eoe(this,
//                       ElemOpEmitter::Kind::Delete,
//                       ElemOpEmitter::ObjKind::Other);
//     oe.emitOptionalJumpLabel();
//     eoe.prepareForObj();
//     emit(obj);
//     oe.emitJumpShortCircuit();
//     eoe.prepareForKey();
//     emit(key);
//     eoe.emitDelete();
//     oe.emitOptionalJumpTarget();
//
//   `print?.(arg);`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     CallOrNewEmitter cone(this, JSOp::Call,
//                           CallOrNewEmitter::ArgumentsKind::Other,
//                           ValueUsage::WantValue);
//     oe.emitOptionalJumpLabel();
//     cone.emitNameCallee(print);
//     cone.emitThis();
//     oe.emitShortCircuitForCall();
//     cone.prepareForNonSpreadArguments();
//     emit(arg);
//     cone.emitEnd(1, Some(offset_of_callee));
//     oe.emitOptionalJumpTarget();
//
//   `callee.prop?.(arg1, arg2);`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     CallOrNewEmitter cone(this, JSOp::Call,
//                           CallOrNewEmitter::ArgumentsKind::Other,
//                           ValueUsage::WantValue);
//     oe.emitOptionalJumpLabel();
//     PropOpEmitter& poe = cone.prepareForPropCallee(false);
//     ... emit `callee.prop` with `poe` here...
//     cone.emitThis();
//     oe.emitShortCircuitForCall();
//     cone.prepareForNonSpreadArguments();
//     emit(arg1);
//     emit(arg2);
//     cone.emitEnd(2, Some(offset_of_callee));
//     oe.emitOptionalJumpTarget();
//
//   `callee[key]?.(arg);`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     CallOrNewEmitter cone(this, JSOp::Call,
//                           CallOrNewEmitter::ArgumentsKind::Other,
//                           ValueUsage::WantValue);
//     oe.emitOptionalJumpLabel();
//     ElemOpEmitter& eoe = cone.prepareForElemCallee(false);
//     ... emit `callee[key]` with `eoe` here...
//     cone.emitThis();
//     oe.emitShortCircuitForCall();
//     cone.prepareForNonSpreadArguments();
//     emit(arg);
//     cone.emitEnd(1, Some(offset_of_callee));
//     oe.emitOptionalJumpTarget();
//
//   `(function() { ... })?.(arg);`
//     OptionalEmitter oe(this, JSOp::Undefined);
//     CallOrNewEmitter cone(this, JSOp::Call,
//                           CallOrNewEmitter::ArgumentsKind::Other,
//                           ValueUsage::WantValue);
//     oe.emitOptionalJumpLabel();
//     cone.prepareForFunctionCallee();
//     emit(function);
//     cone.emitThis();
//     oe.emitShortCircuitForCall();
//     cone.prepareForNonSpreadArguments();
//     emit(arg);
//     cone.emitEnd(1, Some(offset_of_callee));
//     oe.emitOptionalJumpTarget();
//
//   `(a?b)();`
//     OptionalEmitter oe(this, JSOp::Undefined, OptionalEmitter::Kind::Reference);
//     CallOrNewEmitter cone(this, JSOP_CALL,
//                           CallOrNewEmitter::ArgumentsKind::Other,
//                           ValueUsage::WantValue);
//     oe.emitOptionalJumpLabel();
//     cone.prepareForFunctionCallee();
//     emit(optionalChain);
//     cone.emitThis();
//     oe.emitOptionalJumpTarget();
//     oe.emitShortCircuitForCall();
//     cone.prepareForNonSpreadArguments();
//     emit(arg);
//     cone.emitEnd(1, Some(offset_of_callee));
//     oe.emitOptionalJumpTarget();
//
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

    // The state of this emitter.
    //
    // +-------+
    // | Start |
    // +-------+
    //     |
    //     | emitOptionalJumpLabel
    //     v
    // +-------+   emitJumpShortCircuit        +--------------+
    // | Label |-+---------------------------->| ShortCircuit |-----------+
    // +-------+ |                             +--------------+           |
    //    +----->|                                                        |
    //    |      | emitJumpShortCircuitForCall +---------------------+    v
    //    |      +---------------------------->| ShortCircuitForCall |--->+
    //    |                                    +---------------------+    |
    //    |                                                               |
    //     ---------------------------------------------------------------+
    //                                                                    |
    //                                                                    |
    // +------------------------------------------------------------------+
    // |
    // | emitOptionalJumpTarget +---------+
    // +----------------------->| JumpEnd |
    //                          +---------+
    //
#ifdef DEBUG
    enum class State {
      // The initial state.
      Start,

      // The fake jump label
      Label,

      // for shortcircuiting in most cases.
      ShortCircuit,

      // for shortcircuiting from references, which have two items on
      // the stack. For example function calls.
      ShortCircuitForCall,

      // internally used, end of the jump code
      JumpEnd
    };

    State state_ = State::Start;
#endif

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
