/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "frontend/OptionalEmitter.h"

#include "frontend/BytecodeEmitter.h"
#include "frontend/IfEmitter.h"  // IfEmitter, InternalIfEmitter, CondEmitter
#include "frontend/SharedContext.h"
#include "vm/Opcodes.h"
#include "vm/String.h"

using namespace js;
using namespace js::frontend;

OptionalEmitter::OptionalEmitter(BytecodeEmitter* bce, int32_t initialDepth,
                                 JSOp op, Kind kind)
    : bce_(bce), tdzCache_(bce),
      breakInfo_(bce, StatementKind::Label),
      initialDepth_(initialDepth), op_(op), kind_(kind) {}

bool OptionalEmitter::emitOptionalJumpLabel() {
    MOZ_ASSERT(state_ == State::Start);
    if (!bce_->emitJump(JSOP_LABEL, &top_)) {
        return false;
    }
#ifdef DEBUG
    state_ = State::Label;
#endif
    return true;
}

bool OptionalEmitter::emitJumpShortCircuit() {
    MOZ_ASSERT(state_ == State::Label || state_ == State::ShortCircuit ||
               state_ == State::ShortCircuitForCall);
    MOZ_ASSERT(initialDepth_ + 1 == bce_->stackDepth);
    InternalIfEmitter ifEmitter(bce_);
    if (!bce_->emitPushNotUndefinedOrNull())
        return false;

    if (!bce_->emit1(JSOP_NOT))
        return false;

    if (!ifEmitter.emitThen())
        return false;

    // Perform ShortCircuiting code and break
    if (!bce_->emit1(JSOP_POP))
        return false;

    if (!bce_->emit1(op_))
        return false;

    if (kind_ == Kind::Reference) {
        if (!bce_->emit1(op_))
            return false;
    }

    if (!bce_->emitGoto(&breakInfo_, &breakInfo_.breaks, SRC_BREAK2LABEL))
        return false;

    if (!ifEmitter.emitEnd()) {
        return false;
    }
#ifdef DEBUG
    state_ = State::ShortCircuit;
#endif
    return true;
}

bool OptionalEmitter::emitJumpShortCircuitForCall() {
    MOZ_ASSERT(state_ == State::Label || state_ == State::ShortCircuit ||
               state_ == State::ShortCircuitForCall);
    int32_t depth = bce_->stackDepth;
    MOZ_ASSERT(initialDepth_ + 2 == depth);
    if (!bce_->emit1(JSOP_SWAP))
        return false;

    InternalIfEmitter ifEmitter(bce_);
    if (!bce_->emitPushNotUndefinedOrNull())
        return false;

    if (!bce_->emit1(JSOP_NOT))
        return false;

    if (!ifEmitter.emitThen())
        return false;

    // Perform ShortCircuiting code for Call and break
    if (!bce_->emit1(JSOP_POP))
        return false;

    if (!bce_->emit1(JSOP_POP))
        return false;

    if (!bce_->emit1(op_))
        return false;

    if (kind_ == Kind::Reference) {
        if (!bce_->emit1(op_))
            return false;
    }

    if (!bce_->emitGoto(&breakInfo_, &breakInfo_.breaks, SRC_BREAK2LABEL))
        return false;

    if (!ifEmitter.emitEnd())
        return false;

    bce_->stackDepth = depth;

    if (!bce_->emit1(JSOP_SWAP))
        return false;
#ifdef DEBUG
    state_ = State::ShortCircuitForCall;
#endif
    return true;
}

bool OptionalEmitter::emitOptionalJumpTarget() {
    MOZ_ASSERT(state_ == State::ShortCircuit ||
               state_ == State::ShortCircuitForCall);
    // Patch the JSOP_LABEL offset.
    JumpTarget brk{ bce_->lastNonJumpTargetOffset() };
    bce_->patchJumpsToTarget(top_, brk);

    // Patch the emitGoto() offset.
    if (!breakInfo_.patchBreaks(bce_))
        return false;

    // XXX: Commented out due to workaround for missing JSOP_GOTO functionality
    /*// reset stack depth to the depth when we jumped
    bce_->stackDepth = initialDepth_ + 1;*/
#ifdef DEBUG
    state_ = State::JumpEnd;
#endif
    return true;
}
