/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * JS bytecode generation.
 */

#include "frontend/BytecodeEmitter.h"

#include "mozilla/ArrayUtils.h"
#include "mozilla/DebugOnly.h"
#include "mozilla/FloatingPoint.h"
#include "mozilla/Maybe.h"
#include "mozilla/PodOperations.h"

#include <string.h>

#include "jsapi.h"
#include "jsatom.h"
#include "jscntxt.h"
#include "jsfun.h"
#include "jsnum.h"
#include "jsopcode.h"
#include "jsscript.h"
#include "jstypes.h"
#include "jsutil.h"

#include "ds/Nestable.h"
#include "frontend/BytecodeControlStructures.h"
#include "frontend/CallOrNewEmitter.h"
#include "frontend/ElemOpEmitter.h"
#include "frontend/EmitterScope.h"
#include "frontend/ExpressionStatementEmitter.h"
#include "frontend/ForOfLoopControl.h"
#include "frontend/IfEmitter.h"
#include "frontend/LabelEmitter.h"  // LabelEmitter
#include "frontend/NameOpEmitter.h"
#include "frontend/ObjectEmitter.h"  // PropertyEmitter, ObjectEmitter, ClassEmitter
#include "frontend/OptionalEmitter.h"
#include "frontend/Parser.h"
#include "frontend/PropOpEmitter.h"
#include "frontend/TDZCheckCache.h"
#include "frontend/TryEmitter.h"
#include "frontend/TokenStream.h"
#include "vm/Debugger.h"
#include "vm/GeneratorObject.h"
#include "vm/Stack.h"
#include "wasm/AsmJS.h"

#include "jsatominlines.h"
#include "jsobjinlines.h"
#include "jsscriptinlines.h"

#include "frontend/ParseNode-inl.h"
#include "vm/EnvironmentObject-inl.h"
#include "vm/NativeObject-inl.h"

using namespace js;
using namespace js::gc;
using namespace js::frontend;

using mozilla::ArrayLength;
using mozilla::AssertedCast;
using mozilla::DebugOnly;
using mozilla::Maybe;
using mozilla::Nothing;
using mozilla::NumberIsInt32;
using mozilla::PodCopy;
using mozilla::Some;
using mozilla::Unused;

static bool
ParseNodeRequiresSpecialLineNumberNotes(ParseNode* pn)
{
    return pn->getKind() == ParseNodeKind::While || pn->getKind() == ParseNodeKind::For;
}

BytecodeEmitter::BytecodeEmitter(BytecodeEmitter* parent,
                                 const EitherParser<FullParseHandler>& parser, SharedContext* sc,
                                 HandleScript script, Handle<LazyScript*> lazyScript,
                                 uint32_t lineNum, EmitterMode emitterMode)
  : sc(sc),
    cx(sc->context),
    parent(parent),
    script(cx, script),
    lazyScript(cx, lazyScript),
    prologue(cx, lineNum),
    main(cx, lineNum),
    current(&main),
    parser(parser),
    atomIndices(cx->frontendCollectionPool()),
    firstLine(lineNum),
    maxFixedSlots(0),
    maxStackDepth(0),
    stackDepth(0),
    arrayCompDepth(0),
    emitLevel(0),
    bodyScopeIndex(UINT32_MAX),
    varEmitterScope(nullptr),
    innermostNestableControl(nullptr),
    innermostEmitterScope_(nullptr),
    innermostTDZCheckCache(nullptr),
#ifdef DEBUG
    unstableEmitterScope(false),
#endif
    constList(cx),
    scopeList(cx),
    tryNoteList(cx),
    scopeNoteList(cx),
    yieldAndAwaitOffsetList(cx),
    typesetCount(0),
    hasSingletons(false),
    hasTryFinally(false),
    emittingRunOnceLambda(false),
    emitterMode(emitterMode),
    functionBodyEndPosSet(false)
{
    MOZ_ASSERT_IF(emitterMode == LazyFunction, lazyScript);
}

BytecodeEmitter::BytecodeEmitter(BytecodeEmitter* parent,
                                 const EitherParser<FullParseHandler>& parser, SharedContext* sc,
                                 HandleScript script, Handle<LazyScript*> lazyScript,
                                 TokenPos bodyPosition, EmitterMode emitterMode)
    : BytecodeEmitter(parent, parser, sc, script, lazyScript,
                      parser.tokenStream().srcCoords.lineNum(bodyPosition.begin),
                      emitterMode)
{
    setFunctionBodyEndPos(bodyPosition);
}

bool
BytecodeEmitter::init()
{
    return atomIndices.acquire(cx);
}

template <typename T>
T*
BytecodeEmitter::findInnermostNestableControl() const
{
    return NestableControl::findNearest<T>(innermostNestableControl);
}

template <typename T, typename Predicate /* (T*) -> bool */>
T*
BytecodeEmitter::findInnermostNestableControl(Predicate predicate) const
{
    return NestableControl::findNearest<T>(innermostNestableControl, predicate);
}

NameLocation
BytecodeEmitter::lookupName(JSAtom* name)
{
    return innermostEmitterScope()->lookup(this, name);
}

Maybe<NameLocation>
BytecodeEmitter::locationOfNameBoundInScope(JSAtom* name, EmitterScope* target)
{
    return innermostEmitterScope()->locationBoundInScope(name, target);
}

Maybe<NameLocation>
BytecodeEmitter::locationOfNameBoundInFunctionScope(JSAtom* name, EmitterScope* source)
{
    EmitterScope* funScope = source;
    while (!funScope->scope(this)->is<FunctionScope>())
        funScope = funScope->enclosingInFrame();
    return source->locationBoundInScope(name, funScope);
}

bool
BytecodeEmitter::emitCheck(ptrdiff_t delta, ptrdiff_t* offset)
{
    size_t oldLength = code().length();
    *offset = ptrdiff_t(oldLength);

    size_t newLength = oldLength + size_t(delta);
    if (MOZ_UNLIKELY(newLength > MaxBytecodeLength)) {
        ReportAllocationOverflow(cx);
        return false;
    }

    if (!code().growBy(delta)) {
        return false;
    }
    return true;
}

void
BytecodeEmitter::updateDepth(ptrdiff_t target)
{
    jsbytecode* pc = code(target);

    int nuses = StackUses(pc);
    int ndefs = StackDefs(pc);

    stackDepth -= nuses;
    MOZ_ASSERT(stackDepth >= 0);
    stackDepth += ndefs;

    if ((uint32_t)stackDepth > maxStackDepth)
        maxStackDepth = stackDepth;
}

#ifdef DEBUG
bool
BytecodeEmitter::checkStrictOrSloppy(JSOp op)
{
    if (IsCheckStrictOp(op) && !sc->strict())
        return false;
    if (IsCheckSloppyOp(op) && sc->strict())
        return false;
    return true;
}
#endif

bool
BytecodeEmitter::emit1(JSOp op)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));

    ptrdiff_t offset;
    if (!emitCheck(1, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emit2(JSOp op, uint8_t op1)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));

    ptrdiff_t offset;
    if (!emitCheck(2, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    code[1] = jsbytecode(op1);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emit3(JSOp op, jsbytecode op1, jsbytecode op2)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));

    /* These should filter through emitVarOp. */
    MOZ_ASSERT(!IsArgOp(op));
    MOZ_ASSERT(!IsLocalOp(op));

    ptrdiff_t offset;
    if (!emitCheck(3, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    code[1] = op1;
    code[2] = op2;
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emitN(JSOp op, size_t extra, ptrdiff_t* offset)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));
    ptrdiff_t length = 1 + ptrdiff_t(extra);

    ptrdiff_t off;
    if (!emitCheck(length, &off))
        return false;

    jsbytecode* code = this->code(off);
    code[0] = jsbytecode(op);
    /* The remaining |extra| bytes are set by the caller */

    /*
     * Don't updateDepth if op's use-count comes from the immediate
     * operand yet to be stored in the extra bytes after op.
     */
    if (CodeSpec[op].nuses >= 0)
        updateDepth(off);

    if (offset)
        *offset = off;
    return true;
}

bool
BytecodeEmitter::emitJumpTarget(JumpTarget* target)
{
    ptrdiff_t off = offset();

    // Alias consecutive jump targets.
    if (off == current->lastTarget.offset + ptrdiff_t(JSOP_JUMPTARGET_LENGTH)) {
        target->offset = current->lastTarget.offset;
        return true;
    }

    target->offset = off;
    current->lastTarget.offset = off;
    if (!emit1(JSOP_JUMPTARGET))
        return false;
    return true;
}

bool
BytecodeEmitter::emitJumpNoFallthrough(JSOp op, JumpList* jump)
{
    ptrdiff_t offset;
    if (!emitCheck(5, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    MOZ_ASSERT(-1 <= jump->offset && jump->offset < offset);
    jump->push(this->code(0), offset);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emitJump(JSOp op, JumpList* jump)
{
    if (!emitJumpNoFallthrough(op, jump))
        return false;
    if (BytecodeFallsThrough(op)) {
        JumpTarget fallthrough;
        if (!emitJumpTarget(&fallthrough))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::emitBackwardJump(JSOp op, JumpTarget target, JumpList* jump, JumpTarget* fallthrough)
{
    if (!emitJumpNoFallthrough(op, jump))
        return false;
    patchJumpsToTarget(*jump, target);

    // Unconditionally create a fallthrough for closing iterators, and as a
    // target for break statements.
    if (!emitJumpTarget(fallthrough))
        return false;
    return true;
}

void
BytecodeEmitter::patchJumpsToTarget(JumpList jump, JumpTarget target)
{
    MOZ_ASSERT(-1 <= jump.offset && jump.offset <= offset());
    MOZ_ASSERT(0 <= target.offset && target.offset <= offset());
    MOZ_ASSERT_IF(jump.offset != -1 && target.offset + 4 <= offset(),
                  BytecodeIsJumpTarget(JSOp(*code(target.offset))));
    jump.patchAll(code(0), target);
}

bool
BytecodeEmitter::emitJumpTargetAndPatch(JumpList jump)
{
    if (jump.offset == -1)
        return true;
    JumpTarget target;
    if (!emitJumpTarget(&target))
        return false;
    patchJumpsToTarget(jump, target);
    return true;
}

bool
BytecodeEmitter::emitCall(JSOp op, uint16_t argc, const Maybe<uint32_t>& sourceCoordOffset)
{
    if (sourceCoordOffset.isSome()) {
        if (!updateSourceCoordNotes(*sourceCoordOffset))
            return false;
    }
    return emit3(op, ARGC_LO(argc), ARGC_HI(argc));
}

bool
BytecodeEmitter::emitCall(JSOp op, uint16_t argc, ParseNode* pn)
{
    if (pn && !updateSourceCoordNotes(pn->pn_pos.begin))
        return false;
    return emitCall(op, argc, pn ? Some(pn->pn_pos.begin) : Nothing());
}

bool
BytecodeEmitter::emitDupAt(unsigned slotFromTop, unsigned count)
{
    MOZ_ASSERT(slotFromTop < unsigned(stackDepth));

    MOZ_ASSERT(slotFromTop + 1 >= count);

    if (slotFromTop == 0 && count == 1) {
        return emit1(JSOP_DUP);
    }

    if (slotFromTop == 1 && count == 2) {
      return emit1(JSOP_DUP2);
    }

    if (slotFromTop >= JS_BIT(24)) {
        reportError(nullptr, JSMSG_TOO_MANY_LOCALS);
        return false;
    }

    for (unsigned i = 0; i < count; i++) {
        ptrdiff_t off;
        if (!emitN(JSOP_DUPAT, 3, &off)) {
            return false;
        }

        jsbytecode* pc = code(off);
        SET_UINT24(pc, slotFromTop);
    }

    return true;
}

bool
BytecodeEmitter::emitPopN(unsigned n)
{
    MOZ_ASSERT(n != 0);

    if (n == 1)
        return emit1(JSOP_POP);

    // 2 JSOP_POPs (2 bytes) are shorter than JSOP_POPN (3 bytes).
    if (n == 2)
        return emit1(JSOP_POP) && emit1(JSOP_POP);

    return emitUint16Operand(JSOP_POPN, n);
}

bool
BytecodeEmitter::emitPickN(uint8_t n)
{
    MOZ_ASSERT(n != 0);

    if (n == 1) {
      return emit1(JSOP_SWAP);
    }

    return emit2(JSOP_PICK, n);
}

bool
BytecodeEmitter::emitUnpickN(uint8_t n)
{
    MOZ_ASSERT(n != 0);

    if (n == 1) {
      return emit1(JSOP_SWAP);
    }

    return emit2(JSOP_UNPICK, n);
}

bool
BytecodeEmitter::emitCheckIsObj(CheckIsObjectKind kind)
{
    return emit2(JSOP_CHECKISOBJ, uint8_t(kind));
}

bool
BytecodeEmitter::emitCheckIsCallable(CheckIsCallableKind kind)
{
    return emit2(JSOP_CHECKISCALLABLE, uint8_t(kind));
}

static inline unsigned
LengthOfSetLine(unsigned line)
{
    return 1 /* SN_SETLINE */ + (line > SN_4BYTE_OFFSET_MASK ? 4 : 1);
}

/* Updates line number notes, not column notes. */
bool
BytecodeEmitter::updateLineNumberNotes(uint32_t offset)
{
    TokenStreamAnyChars* ts = &parser.tokenStream();
    bool onThisLine;
    if (!ts->srcCoords.isOnThisLine(offset, currentLine(), &onThisLine)) {
        ts->reportErrorNoOffset(JSMSG_OUT_OF_MEMORY);
        return false;
    }

    if (!onThisLine) {
        unsigned line = ts->srcCoords.lineNum(offset);
        unsigned delta = line - currentLine();

        /*
         * Encode any change in the current source line number by using
         * either several SRC_NEWLINE notes or just one SRC_SETLINE note,
         * whichever consumes less space.
         *
         * NB: We handle backward line number deltas (possible with for
         * loops where the update part is emitted after the body, but its
         * line number is <= any line number in the body) here by letting
         * unsigned delta_ wrap to a very large number, which triggers a
         * SRC_SETLINE.
         */
        current->currentLine = line;
        current->lastColumn  = 0;
        if (delta >= LengthOfSetLine(line)) {
            if (!newSrcNote2(SRC_SETLINE, ptrdiff_t(line)))
                return false;
        } else {
            do {
                if (!newSrcNote(SRC_NEWLINE))
                    return false;
            } while (--delta != 0);
        }
    }
    return true;
}

/* Updates the line number and column number information in the source notes. */
bool
BytecodeEmitter::updateSourceCoordNotes(uint32_t offset)
{
    if (!updateLineNumberNotes(offset))
        return false;

    uint32_t columnIndex = parser.tokenStream().srcCoords.columnIndex(offset);
    ptrdiff_t colspan = ptrdiff_t(columnIndex) - ptrdiff_t(current->lastColumn);
    if (colspan != 0) {
        // If the column span is so large that we can't store it, then just
        // discard this information. This can happen with minimized or otherwise
        // machine-generated code. Even gigantic column numbers are still
        // valuable if you have a source map to relate them to something real;
        // but it's better to fail soft here.
        if (!SN_REPRESENTABLE_COLSPAN(colspan))
            return true;
        if (!newSrcNote2(SRC_COLSPAN, SN_COLSPAN_TO_OFFSET(colspan)))
            return false;
        current->lastColumn = columnIndex;
    }
    return true;
}

bool
BytecodeEmitter::emitLoopHead(ParseNode* nextpn, JumpTarget* top)
{
    if (nextpn) {
        /*
         * Try to give the JSOP_LOOPHEAD the same line number as the next
         * instruction. nextpn is often a block, in which case the next
         * instruction typically comes from the first statement inside.
         */
        if (nextpn->isKind(ParseNodeKind::LexicalScope))
            nextpn = nextpn->scopeBody();
        MOZ_ASSERT_IF(nextpn->isKind(ParseNodeKind::StatementList), nextpn->isArity(PN_LIST));
        if (nextpn->isKind(ParseNodeKind::StatementList) && nextpn->pn_head)
            nextpn = nextpn->pn_head;
        if (!updateSourceCoordNotes(nextpn->pn_pos.begin))
            return false;
    }

    *top = { offset() };
    return emit1(JSOP_LOOPHEAD);
}

bool
BytecodeEmitter::emitLoopEntry(ParseNode* nextpn, JumpList entryJump)
{
    if (nextpn) {
        /* Update the line number, as for LOOPHEAD. */
        if (nextpn->isKind(ParseNodeKind::LexicalScope))
            nextpn = nextpn->scopeBody();
        MOZ_ASSERT_IF(nextpn->isKind(ParseNodeKind::StatementList), nextpn->isArity(PN_LIST));
        if (nextpn->isKind(ParseNodeKind::StatementList) && nextpn->pn_head)
            nextpn = nextpn->pn_head;
        if (!updateSourceCoordNotes(nextpn->pn_pos.begin))
            return false;
    }

    JumpTarget entry{ offset() };
    patchJumpsToTarget(entryJump, entry);

    LoopControl& loopInfo = innermostNestableControl->as<LoopControl>();
    MOZ_ASSERT(loopInfo.loopDepth() > 0);

    uint8_t loopDepthAndFlags = PackLoopEntryDepthHintAndFlags(loopInfo.loopDepth(),
                                                               loopInfo.canIonOsr());
    return emit2(JSOP_LOOPENTRY, loopDepthAndFlags);
}

void
BytecodeEmitter::checkTypeSet(JSOp op)
{
    if (CodeSpec[op].format & JOF_TYPESET) {
        if (typesetCount < UINT16_MAX)
            typesetCount++;
    }
}

bool
BytecodeEmitter::emitUint16Operand(JSOp op, uint32_t operand)
{
    MOZ_ASSERT(operand <= UINT16_MAX);
    if (!emit3(op, UINT16_LO(operand), UINT16_HI(operand)))
        return false;
    checkTypeSet(op);
    return true;
}

bool
BytecodeEmitter::emitUint32Operand(JSOp op, uint32_t operand)
{
    ptrdiff_t off;
    if (!emitN(op, 4, &off))
        return false;
    SET_UINT32(code(off), operand);
    checkTypeSet(op);
    return true;
}

namespace {

class NonLocalExitControl
{
  public:
    enum Kind
    {
        // IteratorClose is handled especially inside the exception unwinder.
        Throw,

        // A 'continue' statement does not call IteratorClose for the loop it
        // is continuing, i.e. excluding the target loop.
        Continue,

        // A 'break' or 'return' statement does call IteratorClose for the
        // loop it is breaking out of or returning from, i.e. including the
        // target loop.
        Break,
        Return
    };

  private:
    BytecodeEmitter* bce_;
    const uint32_t savedScopeNoteIndex_;
    const int savedDepth_;
    uint32_t openScopeNoteIndex_;
    Kind kind_;

    NonLocalExitControl(const NonLocalExitControl&) = delete;

    MOZ_MUST_USE bool leaveScope(EmitterScope* scope);

  public:
    NonLocalExitControl(BytecodeEmitter* bce, Kind kind)
      : bce_(bce),
        savedScopeNoteIndex_(bce->scopeNoteList.length()),
        savedDepth_(bce->stackDepth),
        openScopeNoteIndex_(bce->innermostEmitterScope()->noteIndex()),
        kind_(kind)
    { }

    ~NonLocalExitControl() {
        for (uint32_t n = savedScopeNoteIndex_; n < bce_->scopeNoteList.length(); n++)
            bce_->scopeNoteList.recordEnd(n, bce_->offset(), bce_->inPrologue());
        bce_->stackDepth = savedDepth_;
    }

    MOZ_MUST_USE bool prepareForNonLocalJump(NestableControl* target);

    MOZ_MUST_USE bool prepareForNonLocalJumpToOutermost() {
        return prepareForNonLocalJump(nullptr);
    }
};

bool
NonLocalExitControl::leaveScope(EmitterScope* es)
{
    if (!es->leave(bce_, /* nonLocal = */ true))
        return false;

    // As we pop each scope due to the non-local jump, emit notes that
    // record the extent of the enclosing scope. These notes will have
    // their ends recorded in ~NonLocalExitControl().
    uint32_t enclosingScopeIndex = ScopeNote::NoScopeIndex;
    if (es->enclosingInFrame())
        enclosingScopeIndex = es->enclosingInFrame()->index();
    if (!bce_->scopeNoteList.append(enclosingScopeIndex, bce_->offset(), bce_->inPrologue(),
                                    openScopeNoteIndex_))
        return false;
    openScopeNoteIndex_ = bce_->scopeNoteList.length() - 1;

    return true;
}

/*
 * Emit additional bytecode(s) for non-local jumps.
 */
bool
NonLocalExitControl::prepareForNonLocalJump(NestableControl* target)
{
    EmitterScope* es = bce_->innermostEmitterScope();
    int npops = 0;

    AutoCheckUnstableEmitterScope cues(bce_);

    // For 'continue', 'break', and 'return' statements, emit IteratorClose
    // bytecode inline. 'continue' statements do not call IteratorClose for
    // the loop they are continuing.
    bool emitIteratorClose = kind_ == Continue || kind_ == Break || kind_ == Return;
    bool emitIteratorCloseAtTarget = emitIteratorClose && kind_ != Continue;

    auto flushPops = [&npops](BytecodeEmitter* bce) {
        if (npops && !bce->emitPopN(npops))
            return false;
        npops = 0;
        return true;
    };

    // Walk the nestable control stack and patch jumps.
    for (NestableControl* control = bce_->innermostNestableControl;
         control != target;
         control = control->enclosing())
    {
        // Walk the scope stack and leave the scopes we entered. Leaving a scope
        // may emit administrative ops like JSOP_POPLEXICALENV but never anything
        // that manipulates the stack.
        for (; es != control->emitterScope(); es = es->enclosingInFrame()) {
            if (!leaveScope(es))
                return false;
        }

        switch (control->kind()) {
          case StatementKind::Finally: {
            TryFinallyControl& finallyControl = control->as<TryFinallyControl>();
            if (finallyControl.emittingSubroutine()) {
                /*
                 * There's a [exception or hole, retsub pc-index] pair and the
                 * possible return value on the stack that we need to pop.
                 */
                npops += 3;
            } else {
                if (!flushPops(bce_))
                    return false;
                if (!bce_->emitJump(JSOP_GOSUB, &finallyControl.gosubs)) // ...
                    return false;
            }
            break;
          }

          case StatementKind::ForOfLoop:
            if (emitIteratorClose) {
                if (!flushPops(bce_))
                    return false;

                ForOfLoopControl& loopinfo = control->as<ForOfLoopControl>();
                if (!loopinfo.emitPrepareForNonLocalJumpFromScope(bce_, *es,
                                                                  /* isTarget = */ false))
                {                                         // ...
                    return false;
                }
            } else {
                npops += 2;
            }
            break;

          case StatementKind::ForInLoop:
            if (!flushPops(bce_))
                return false;

            // The iterator and the current value are on the stack.
            if (!bce_->emit1(JSOP_POP))                   // ... ITER
                return false;
            if (!bce_->emit1(JSOP_ENDITER))               // ...
                return false;
            break;

          default:
            break;
        }
    }

    if (!flushPops(bce_))
        return false;

    if (target && emitIteratorCloseAtTarget && target->is<ForOfLoopControl>()) {
        ForOfLoopControl& loopinfo = target->as<ForOfLoopControl>();
        if (!loopinfo.emitPrepareForNonLocalJumpFromScope(bce_, *es,
                                                          /* isTarget = */ true))
        {                                                 // ... UNDEF UNDEF UNDEF
            return false;
        }
    }

    EmitterScope* targetEmitterScope = target ? target->emitterScope() : bce_->varEmitterScope;
    for (; es != targetEmitterScope; es = es->enclosingInFrame()) {
        if (!leaveScope(es))
            return false;
    }

    return true;
}

}  // anonymous namespace

bool
BytecodeEmitter::emitGoto(NestableControl* target, JumpList* jumplist, SrcNoteType noteType)
{
    NonLocalExitControl nle(this, noteType == SRC_CONTINUE
                                  ? NonLocalExitControl::Continue
                                  : NonLocalExitControl::Break);

    if (!nle.prepareForNonLocalJump(target))
        return false;

    if (noteType != SRC_NULL) {
        if (!newSrcNote(noteType))
            return false;
    }

    return emitJump(JSOP_GOTO, jumplist);
}

Scope*
BytecodeEmitter::innermostScope() const
{
    return innermostEmitterScope()->scope(this);
}

bool
BytecodeEmitter::emitIndex32(JSOp op, uint32_t index)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));

    const size_t len = 1 + UINT32_INDEX_LEN;
    MOZ_ASSERT(len == size_t(CodeSpec[op].length));

    ptrdiff_t offset;
    if (!emitCheck(len, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    SET_UINT32_INDEX(code, index);
    checkTypeSet(op);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emitIndexOp(JSOp op, uint32_t index)
{
    MOZ_ASSERT(checkStrictOrSloppy(op));

    const size_t len = CodeSpec[op].length;
    MOZ_ASSERT(len >= 1 + UINT32_INDEX_LEN);

    ptrdiff_t offset;
    if (!emitCheck(len, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = jsbytecode(op);
    SET_UINT32_INDEX(code, index);
    checkTypeSet(op);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::emitAtomOp(JSAtom* atom, JSOp op)
{
    MOZ_ASSERT(atom);

    // .generator lookups should be emitted as JSOP_GETALIASEDVAR instead of
    // JSOP_GETNAME etc, to bypass |with| objects on the scope chain.
    // It's safe to emit .this lookups though because |with| objects skip
    // those.
    MOZ_ASSERT_IF(op == JSOP_GETNAME || op == JSOP_GETGNAME,
                  atom != cx->names().dotGenerator);

    if (op == JSOP_GETPROP && atom == cx->names().length) {
        /* Specialize length accesses for the interpreter. */
        op = JSOP_LENGTH;
    }

    uint32_t index;
    if (!makeAtomIndex(atom, &index))
        return false;

    return emitAtomOp(index, op);
}

bool
BytecodeEmitter::emitAtomOp(uint32_t atomIndex, JSOp op)
{
    MOZ_ASSERT(JOF_OPTYPE(op) == JOF_ATOM);

    return emitIndexOp(op, atomIndex);
}

bool
BytecodeEmitter::emitInternedScopeOp(uint32_t index, JSOp op)
{
    MOZ_ASSERT(JOF_OPTYPE(op) == JOF_SCOPE);
    MOZ_ASSERT(index < scopeList.length());
    return emitIndex32(op, index);
}

bool
BytecodeEmitter::emitInternedObjectOp(uint32_t index, JSOp op)
{
    MOZ_ASSERT(JOF_OPTYPE(op) == JOF_OBJECT);
    MOZ_ASSERT(index < objectList.length);
    return emitIndex32(op, index);
}

bool
BytecodeEmitter::emitObjectOp(ObjectBox* objbox, JSOp op)
{
    return emitInternedObjectOp(objectList.add(objbox), op);
}

bool
BytecodeEmitter::emitObjectPairOp(ObjectBox* objbox1, ObjectBox* objbox2, JSOp op)
{
    uint32_t index = objectList.add(objbox1);
    objectList.add(objbox2);
    return emitInternedObjectOp(index, op);
}

bool
BytecodeEmitter::emitRegExp(uint32_t index)
{
    return emitIndex32(JSOP_REGEXP, index);
}

bool
BytecodeEmitter::emitLocalOp(JSOp op, uint32_t slot)
{
    MOZ_ASSERT(JOF_OPTYPE(op) != JOF_ENVCOORD);
    MOZ_ASSERT(IsLocalOp(op));

    ptrdiff_t off;
    if (!emitN(op, LOCALNO_LEN, &off))
        return false;

    SET_LOCALNO(code(off), slot);
    return true;
}

bool
BytecodeEmitter::emitArgOp(JSOp op, uint16_t slot)
{
    MOZ_ASSERT(IsArgOp(op));
    ptrdiff_t off;
    if (!emitN(op, ARGNO_LEN, &off))
        return false;

    SET_ARGNO(code(off), slot);
    return true;
}

bool
BytecodeEmitter::emitEnvCoordOp(JSOp op, EnvironmentCoordinate ec)
{
    MOZ_ASSERT(JOF_OPTYPE(op) == JOF_ENVCOORD);

    unsigned n = ENVCOORD_HOPS_LEN + ENVCOORD_SLOT_LEN;
    MOZ_ASSERT(int(n) + 1 /* op */ == CodeSpec[op].length);

    ptrdiff_t off;
    if (!emitN(op, n, &off))
        return false;

    jsbytecode* pc = code(off);
    SET_ENVCOORD_HOPS(pc, ec.hops());
    pc += ENVCOORD_HOPS_LEN;
    SET_ENVCOORD_SLOT(pc, ec.slot());
    pc += ENVCOORD_SLOT_LEN;
    checkTypeSet(op);
    return true;
}

JSOp
BytecodeEmitter::strictifySetNameOp(JSOp op)
{
    switch (op) {
      case JSOP_SETNAME:
        if (sc->strict())
            op = JSOP_STRICTSETNAME;
        break;
      case JSOP_SETGNAME:
        if (sc->strict())
            op = JSOP_STRICTSETGNAME;
        break;
        default:;
    }
    return op;
}

bool
BytecodeEmitter::checkSideEffects(ParseNode* pn, bool* answer)
{
    if (!CheckRecursionLimit(cx))
        return false;

 restart:

    switch (pn->getKind()) {
      // Trivial cases with no side effects.
      case ParseNodeKind::EmptyStatement:
      case ParseNodeKind::String:
      case ParseNodeKind::TemplateString:
      case ParseNodeKind::RegExp:
      case ParseNodeKind::True:
      case ParseNodeKind::False:
      case ParseNodeKind::Null:
      case ParseNodeKind::RawUndefined:
      case ParseNodeKind::Elision:
      case ParseNodeKind::Generator:
      case ParseNodeKind::Number:
      case ParseNodeKind::ObjectPropertyName:
        MOZ_ASSERT(pn->isArity(PN_NULLARY));
        *answer = false;
        return true;

      // |this| can throw in derived class constructors, including nested arrow
      // functions or eval.
      case ParseNodeKind::This:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = sc->needsThisTDZChecks();
        return true;

      // Trivial binary nodes with more token pos holders.
      case ParseNodeKind::NewTarget:
      case ParseNodeKind::ImportMeta:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        MOZ_ASSERT(pn->pn_left->isKind(ParseNodeKind::PosHolder));
        MOZ_ASSERT(pn->pn_right->isKind(ParseNodeKind::PosHolder));
        *answer = false;
        return true;

      case ParseNodeKind::Break:
      case ParseNodeKind::Continue:
      case ParseNodeKind::Debugger:
        MOZ_ASSERT(pn->isArity(PN_NULLARY));
        *answer = true;
        return true;

      // Watch out for getters!
      case ParseNodeKind::OptionalDot:
      case ParseNodeKind::Dot:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // Unary cases with side effects only if the child has them.
      case ParseNodeKind::TypeOfExpr:
      case ParseNodeKind::Void:
      case ParseNodeKind::Not:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        return checkSideEffects(pn->pn_kid, answer);

      // Even if the name expression is effect-free, performing ToPropertyKey on
      // it might not be effect-free:
      //
      //   RegExp.prototype.toString = () => { throw 42; };
      //   ({ [/regex/]: 0 }); // ToPropertyKey(/regex/) throws 42
      //
      //   function Q() {
      //     ({ [new.target]: 0 });
      //   }
      //   Q.toString = () => { throw 17; };
      //   new Q; // new.target will be Q, ToPropertyKey(Q) throws 17
      case ParseNodeKind::ComputedName:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // Looking up or evaluating the associated name could throw.
      case ParseNodeKind::TypeOfName:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // These unary cases have side effects on the enclosing object/array,
      // sure.  But that's not the question this function answers: it's
      // whether the operation may have a side effect on something *other* than
      // the result of the overall operation in which it's embedded.  The
      // answer to that is no, for an object literal having a mutated prototype
      // and an array comprehension containing no other effectful operations
      // only produce a value, without affecting anything else.
      case ParseNodeKind::MutateProto:
      case ParseNodeKind::ArrayPush:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        return checkSideEffects(pn->pn_kid, answer);

      // Unary cases with obvious side effects.
      case ParseNodeKind::PreIncrement:
      case ParseNodeKind::PostIncrement:
      case ParseNodeKind::PreDecrement:
      case ParseNodeKind::PostDecrement:
      case ParseNodeKind::Throw:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // These might invoke valueOf/toString, even with a subexpression without
      // side effects!  Consider |+{ valueOf: null, toString: null }|.
      case ParseNodeKind::BitNot:
      case ParseNodeKind::Pos:
      case ParseNodeKind::Neg:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // This invokes the (user-controllable) iterator protocol.
      case ParseNodeKind::Spread:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      case ParseNodeKind::InitialYield:
      case ParseNodeKind::YieldStar:
      case ParseNodeKind::Yield:
      case ParseNodeKind::Await:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // Deletion generally has side effects, even if isolated cases have none.
      case ParseNodeKind::DeleteName:
      case ParseNodeKind::DeleteProp:
      case ParseNodeKind::DeleteElem:
      case ParseNodeKind::DeleteOptionalChain:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      // Deletion of a non-Reference expression has side effects only through
      // evaluating the expression.
      case ParseNodeKind::DeleteExpr: {
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        ParseNode* expr = pn->pn_kid;
        return checkSideEffects(expr, answer);
      }

      case ParseNodeKind::ExpressionStatement:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        return checkSideEffects(pn->pn_kid, answer);

      // Binary cases with obvious side effects.
      case ParseNodeKind::Assign:
      case ParseNodeKind::AddAssign:
      case ParseNodeKind::SubAssign:
      case ParseNodeKind::CoalesceAssignExpr:
      case ParseNodeKind::OrAssignExpr:
      case ParseNodeKind::AndAssignExpr:
      case ParseNodeKind::BitOrAssign:
      case ParseNodeKind::BitXorAssign:
      case ParseNodeKind::BitAndAssign:
      case ParseNodeKind::LshAssign:
      case ParseNodeKind::RshAssign:
      case ParseNodeKind::UrshAssign:
      case ParseNodeKind::MulAssign:
      case ParseNodeKind::DivAssign:
      case ParseNodeKind::ModAssign:
      case ParseNodeKind::PowAssign:
      case ParseNodeKind::SetThis:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      case ParseNodeKind::StatementList:
      case ParseNodeKind::CatchList:
      // Strict equality operations and short circuit operators are well-behaved
      // and perform no conversions.
      case ParseNodeKind::CoalesceExpr:
      case ParseNodeKind::Or:
      case ParseNodeKind::And:
      case ParseNodeKind::StrictEq:
      case ParseNodeKind::StrictNe:
      // Any subexpression of a comma expression could be effectful.
      case ParseNodeKind::Comma:
        MOZ_ASSERT(pn->pn_count > 0);
        MOZ_FALLTHROUGH;
      // Subcomponents of a literal may be effectful.
      case ParseNodeKind::Array:
      case ParseNodeKind::Object:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        for (ParseNode* item = pn->pn_head; item; item = item->pn_next) {
            if (!checkSideEffects(item, answer))
                return false;
            if (*answer)
                return true;
        }
        return true;

      // Most other binary operations (parsed as lists in SpiderMonkey) may
      // perform conversions triggering side effects.  Math operations perform
      // ToNumber and may fail invoking invalid user-defined toString/valueOf:
      // |5 < { toString: null }|.  |instanceof| throws if provided a
      // non-object constructor: |null instanceof null|.  |in| throws if given
      // a non-object RHS: |5 in null|.
      case ParseNodeKind::BitOr:
      case ParseNodeKind::BitXor:
      case ParseNodeKind::BitAnd:
      case ParseNodeKind::Eq:
      case ParseNodeKind::Ne:
      case ParseNodeKind::Lt:
      case ParseNodeKind::Le:
      case ParseNodeKind::Gt:
      case ParseNodeKind::Ge:
      case ParseNodeKind::InstanceOf:
      case ParseNodeKind::In:
      case ParseNodeKind::Lsh:
      case ParseNodeKind::Rsh:
      case ParseNodeKind::Ursh:
      case ParseNodeKind::Add:
      case ParseNodeKind::Sub:
      case ParseNodeKind::Star:
      case ParseNodeKind::Div:
      case ParseNodeKind::Mod:
      case ParseNodeKind::Pow:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        MOZ_ASSERT(pn->pn_count >= 2);
        *answer = true;
        return true;

      case ParseNodeKind::Colon:
      case ParseNodeKind::Case:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        if (!checkSideEffects(pn->pn_left, answer))
            return false;
        if (*answer)
            return true;
        return checkSideEffects(pn->pn_right, answer);

      // More getters.
      case ParseNodeKind::OptionalElem:
      case ParseNodeKind::Elem:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // These affect visible names in this code, or in other code.
      case ParseNodeKind::Import:
      case ParseNodeKind::ExportFrom:
      case ParseNodeKind::ExportDefault:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // Likewise.
      case ParseNodeKind::Export:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      case ParseNodeKind::CallImport:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // Every part of a loop might be effect-free, but looping infinitely *is*
      // an effect.  (Language lawyer trivia: C++ says threads can be assumed
      // to exit or have side effects, C++14 [intro.multithread]p27, so a C++
      // implementation's equivalent of the below could set |*answer = false;|
      // if all loop sub-nodes set |*answer = false|!)
      case ParseNodeKind::DoWhile:
      case ParseNodeKind::While:
      case ParseNodeKind::For:
      case ParseNodeKind::ComprehensionFor:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // Declarations affect the name set of the relevant scope.
      case ParseNodeKind::Var:
      case ParseNodeKind::Const:
      case ParseNodeKind::Let:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        *answer = true;
        return true;

      case ParseNodeKind::If:
      case ParseNodeKind::Conditional:
        MOZ_ASSERT(pn->isArity(PN_TERNARY));
        if (!checkSideEffects(pn->pn_kid1, answer))
            return false;
        if (*answer)
            return true;
        if (!checkSideEffects(pn->pn_kid2, answer))
            return false;
        if (*answer)
            return true;
        if ((pn = pn->pn_kid3))
            goto restart;
        return true;

      // Function calls can invoke non-local code.
      case ParseNodeKind::New:
      case ParseNodeKind::Call:
      case ParseNodeKind::OptionalCall:
      case ParseNodeKind::TaggedTemplate:
      case ParseNodeKind::SuperCall:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      // Function arg lists can contain arbitrary expressions. Technically
      // this only causes side-effects if one of the arguments does, but since
      // the call being made will always trigger side-effects, it isn't needed.
      case ParseNodeKind::Arguments:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        *answer = true;
        return true;

      case ParseNodeKind::OptionalChain:
        MOZ_ASSERT(pn->isArity(PN_UNARY));
        *answer = true;
        return true;

      case ParseNodeKind::Pipeline:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        MOZ_ASSERT(pn->pn_count >= 2);
        *answer = true;
        return true;

      // Classes typically introduce names.  Even if no name is introduced,
      // the heritage and/or class body (through computed property names)
      // usually have effects.
      case ParseNodeKind::Class:
        MOZ_ASSERT(pn->isArity(PN_TERNARY));
        *answer = true;
        return true;

      // |with| calls |ToObject| on its expression and so throws if that value
      // is null/undefined.
      case ParseNodeKind::With:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      case ParseNodeKind::Return:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      case ParseNodeKind::Name:
        MOZ_ASSERT(pn->isArity(PN_NAME));
        *answer = true;
        return true;

      // Shorthands could trigger getters: the |x| in the object literal in
      // |with ({ get x() { throw 42; } }) ({ x });|, for example, triggers
      // one.  (Of course, it isn't necessary to use |with| for a shorthand to
      // trigger a getter.)
      case ParseNodeKind::Shorthand:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        *answer = true;
        return true;

      case ParseNodeKind::Function:
        MOZ_ASSERT(pn->isArity(PN_CODE));
        /*
         * A named function, contrary to ES3, is no longer effectful, because
         * we bind its name lexically (using JSOP_CALLEE) instead of creating
         * an Object instance and binding a readonly, permanent property in it
         * (the object and binding can be detected and hijacked or captured).
         * This is a bug fix to ES3; it is fixed in ES3.1 drafts.
         */
        *answer = false;
        return true;

      case ParseNodeKind::Module:
        *answer = false;
        return true;

      // Generator expressions have no side effects on their own.
      case ParseNodeKind::GenExp:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        *answer = false;
        return true;

      case ParseNodeKind::Try:
        MOZ_ASSERT(pn->isArity(PN_TERNARY));
        if (!checkSideEffects(pn->pn_kid1, answer))
            return false;
        if (*answer)
            return true;
        if (ParseNode* catchList = pn->pn_kid2) {
            MOZ_ASSERT(catchList->isKind(ParseNodeKind::CatchList));
            if (!checkSideEffects(catchList, answer))
                return false;
            if (*answer)
                return true;
        }
        if (ParseNode* finallyBlock = pn->pn_kid3) {
            if (!checkSideEffects(finallyBlock, answer))
                return false;
        }
        return true;

      case ParseNodeKind::Catch:
        MOZ_ASSERT(pn->isArity(PN_TERNARY));
        if (ParseNode* name = pn->pn_kid1) {
            if (!checkSideEffects(name, answer))
                return false;
            if (*answer)
                return true;
        }
        if (ParseNode* cond = pn->pn_kid2) {
            if (!checkSideEffects(cond, answer))
                return false;
            if (*answer)
                return true;
        }
        return checkSideEffects(pn->pn_kid3, answer);

      case ParseNodeKind::Switch:
        MOZ_ASSERT(pn->isArity(PN_BINARY));
        if (!checkSideEffects(pn->pn_left, answer))
            return false;
        return *answer || checkSideEffects(pn->pn_right, answer);

      case ParseNodeKind::Label:
        MOZ_ASSERT(pn->isArity(PN_NAME));
        return checkSideEffects(pn->expr(), answer);

      case ParseNodeKind::LexicalScope:
        MOZ_ASSERT(pn->isArity(PN_SCOPE));
        return checkSideEffects(pn->scopeBody(), answer);

      // We could methodically check every interpolated expression, but it's
      // probably not worth the trouble.  Treat template strings as effect-free
      // only if they don't contain any substitutions.
      case ParseNodeKind::TemplateStringList:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        MOZ_ASSERT(pn->pn_count > 0);
        MOZ_ASSERT((pn->pn_count % 2) == 1,
                   "template strings must alternate template and substitution "
                   "parts");
        *answer = pn->pn_count > 1;
        return true;

      case ParseNodeKind::ArrayComp:
        MOZ_ASSERT(pn->isArity(PN_LIST));
        MOZ_ASSERT(pn->pn_count == 1);
        return checkSideEffects(pn->pn_head, answer);

      // This should be unreachable but is left as-is for now.
      case ParseNodeKind::ParamsBody:
        *answer = true;
        return true;

      case ParseNodeKind::ForIn:            // byParseNodeKind::For/ComprehensionFor;
      case ParseNodeKind::ForOf:            // byParseNodeKind::For/ComprehensionFor;
      case ParseNodeKind::ForHead:          // byParseNodeKind::For/ComprehensionFor;
      case ParseNodeKind::ClassMethod:      // byParseNodeKind::Class
      case ParseNodeKind::ClassNames:       // byParseNodeKind::Class
      case ParseNodeKind::ClassMethodList:  // byParseNodeKind::Class
      case ParseNodeKind::ImportSpecList:   // byParseNodeKind::Import
      case ParseNodeKind::ImportSpec:       // byParseNodeKind::Import
      case ParseNodeKind::ExportBatchSpec:  // byParseNodeKind::Export
      case ParseNodeKind::ExportSpecList:   // byParseNodeKind::Export
      case ParseNodeKind::ExportSpec:       // byParseNodeKind::Export
      case ParseNodeKind::CallSiteObj:      // byParseNodeKind::TaggedTemplate
      case ParseNodeKind::PosHolder:        // byParseNodeKind::NewTarget
      case ParseNodeKind::SuperBase:        // byParseNodeKind::Elem and others
      case ParseNodeKind::PropertyName:     // by ParseNodeKind::Dot
        MOZ_CRASH("handled by parent nodes");

      case ParseNodeKind::Limit: // invalid sentinel value
        MOZ_CRASH("invalid node kind");
    }

    MOZ_CRASH("invalid, unenumerated ParseNodeKind value encountered in "
              "BytecodeEmitter::checkSideEffects");
}

bool
BytecodeEmitter::isInLoop()
{
    return findInnermostNestableControl<LoopControl>();
}

bool
BytecodeEmitter::checkSingletonContext()
{
    if (!script->treatAsRunOnce() || sc->isFunctionBox() || isInLoop())
        return false;
    hasSingletons = true;
    return true;
}

bool
BytecodeEmitter::checkRunOnceContext()
{
    return checkSingletonContext() || (!isInLoop() && isRunOnceLambda());
}

bool
BytecodeEmitter::needsImplicitThis()
{
    // Short-circuit if there is an enclosing 'with' scope.
    if (sc->inWith())
        return true;

    // Otherwise see if the current point is under a 'with'.
    for (EmitterScope* es = innermostEmitterScope(); es; es = es->enclosingInFrame()) {
        if (es->scope(this)->kind() == ScopeKind::With)
            return true;
    }

    return false;
}

bool
BytecodeEmitter::maybeSetDisplayURL()
{
    if (tokenStream().hasDisplayURL()) {
        if (!parser.ss()->setDisplayURL(cx, tokenStream().displayURL()))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::maybeSetSourceMap()
{
    if (tokenStream().hasSourceMapURL()) {
        MOZ_ASSERT(!parser.ss()->hasSourceMapURL());
        if (!parser.ss()->setSourceMapURL(cx, tokenStream().sourceMapURL()))
            return false;
    }

    /*
     * Source map URLs passed as a compile option (usually via a HTTP source map
     * header) override any source map urls passed as comment pragmas.
     */
    if (parser.options().sourceMapURL()) {
        // Warn about the replacement, but use the new one.
        if (parser.ss()->hasSourceMapURL()) {
            if (!parser.warningNoOffset(JSMSG_ALREADY_HAS_PRAGMA,
                                        parser.ss()->filename(), "//# sourceMappingURL"))
            {
                return false;
            }
        }

        if (!parser.ss()->setSourceMapURL(cx, parser.options().sourceMapURL()))
            return false;
    }

    return true;
}

void
BytecodeEmitter::tellDebuggerAboutCompiledScript(JSContext* cx)
{
    // Note: when parsing off thread the resulting scripts need to be handed to
    // the debugger after rejoining to the main thread.
    if (cx->helperThread())
        return;

    // Lazy scripts are never top level (despite always being invoked with a
    // nullptr parent), and so the hook should never be fired.
    if (emitterMode != LazyFunction && !parent)
        Debugger::onNewScript(cx, script);
}

inline TokenStreamAnyChars&
BytecodeEmitter::tokenStream()
{
    return parser.tokenStream();
}

void
BytecodeEmitter::reportError(ParseNode* pn, unsigned errorNumber, ...)
{
    TokenPos pos = pn ? pn->pn_pos : tokenStream().currentToken().pos;

    va_list args;
    va_start(args, errorNumber);

    ErrorMetadata metadata;
    if (parser.computeErrorMetadata(&metadata, pos.begin))
        ReportCompileError(cx, Move(metadata), nullptr, JSREPORT_ERROR, errorNumber, args);

    va_end(args);
}

bool
BytecodeEmitter::reportExtraWarning(ParseNode* pn, unsigned errorNumber, ...)
{
    TokenPos pos = pn ? pn->pn_pos : tokenStream().currentToken().pos;

    va_list args;
    va_start(args, errorNumber);

    bool result = parser.reportExtraWarningErrorNumberVA(nullptr, pos.begin, errorNumber, &args);

    va_end(args);
    return result;
}

bool
BytecodeEmitter::emitNewInit(JSProtoKey key)
{
    const size_t len = 1 + UINT32_INDEX_LEN;
    ptrdiff_t offset;
    if (!emitCheck(len, &offset))
        return false;

    jsbytecode* code = this->code(offset);
    code[0] = JSOP_NEWINIT;
    code[1] = jsbytecode(key);
    code[2] = 0;
    code[3] = 0;
    code[4] = 0;
    checkTypeSet(JSOP_NEWINIT);
    updateDepth(offset);
    return true;
}

bool
BytecodeEmitter::iteratorResultShape(unsigned* shape)
{
    // No need to do any guessing for the object kind, since we know exactly how
    // many properties we plan to have.
    gc::AllocKind kind = gc::GetGCObjectKind(2);
    RootedPlainObject obj(cx, NewBuiltinClassInstance<PlainObject>(cx, kind, TenuredObject));
    if (!obj)
        return false;

    Rooted<jsid> value_id(cx, NameToId(cx->names().value));
    Rooted<jsid> done_id(cx, NameToId(cx->names().done));
    if (!NativeDefineProperty(cx, obj, value_id, UndefinedHandleValue, nullptr, nullptr,
                              JSPROP_ENUMERATE))
    {
        return false;
    }
    if (!NativeDefineProperty(cx, obj, done_id, UndefinedHandleValue, nullptr, nullptr,
                              JSPROP_ENUMERATE))
    {
        return false;
    }

    ObjectBox* objbox = parser.newObjectBox(obj);
    if (!objbox)
        return false;

    *shape = objectList.add(objbox);

    return true;
}

bool
BytecodeEmitter::emitPrepareIteratorResult()
{
    unsigned shape;
    if (!iteratorResultShape(&shape))
        return false;
    return emitIndex32(JSOP_NEWOBJECT, shape);
}

bool
BytecodeEmitter::emitFinishIteratorResult(bool done)
{
    uint32_t value_id;
    if (!makeAtomIndex(cx->names().value, &value_id))
        return false;
    uint32_t done_id;
    if (!makeAtomIndex(cx->names().done, &done_id))
        return false;

    if (!emitIndex32(JSOP_INITPROP, value_id))
        return false;
    if (!emit1(done ? JSOP_TRUE : JSOP_FALSE))
        return false;
    if (!emitIndex32(JSOP_INITPROP, done_id))
        return false;
    return true;
}

bool
BytecodeEmitter::emitGetNameAtLocation(JSAtom* name, const NameLocation& loc)
{
    NameOpEmitter noe(this, name, loc, NameOpEmitter::Kind::Get);
    if (!noe.emitGet()) {
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitGetName(ParseNode* pn)
{
    return emitGetName(pn->name());
}

bool
BytecodeEmitter::emitTDZCheckIfNeeded(JSAtom* name, const NameLocation& loc)
{
    // Dynamic accesses have TDZ checks built into their VM code and should
    // never emit explicit TDZ checks.
    MOZ_ASSERT(loc.hasKnownSlot());
    MOZ_ASSERT(loc.isLexical());

    Maybe<MaybeCheckTDZ> check = innermostTDZCheckCache->needsTDZCheck(this, name);
    if (!check)
        return false;

    // We've already emitted a check in this basic block.
    if (*check == DontCheckTDZ)
        return true;

    if (loc.kind() == NameLocation::Kind::FrameSlot) {
        if (!emitLocalOp(JSOP_CHECKLEXICAL, loc.frameSlot()))
            return false;
    } else {
        if (!emitEnvCoordOp(JSOP_CHECKALIASEDLEXICAL, loc.environmentCoordinate()))
            return false;
    }

    return innermostTDZCheckCache->noteTDZCheck(this, name, DontCheckTDZ);
}

bool
BytecodeEmitter::emitPropLHS(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Dot));
    MOZ_ASSERT(!pn->as<PropertyAccess>().isSuper());

    ParseNode* pn2 = pn->pn_left;

    /*
     * If the object operand is also a dotted property reference, reverse the
     * list linked via pn_left temporarily so we can iterate over it from the
     * bottom up (reversing again as we go), to avoid excessive recursion.
     */
    if (pn2->isKind(ParseNodeKind::Dot) && !pn2->as<PropertyAccess>().isSuper()) {
        ParseNode* pndot = pn2;
        ParseNode* pnup = nullptr;
        ParseNode* pndown;
        for (;;) {
            /* Reverse pndot->pn_left to point up, not down. */
            pndown = pndot->pn_left;
            pndot->pn_left = pnup;
            if (!pndown->isKind(ParseNodeKind::Dot) || pndown->as<PropertyAccess>().isSuper())
                break;
            pnup = pndot;
            pndot = pndown;
        }

        /* pndown is a primary expression, not a dotted property reference. */
        if (!emitTree(pndown))
            return false;

        do {
            /* Walk back up the list, emitting annotated name ops. */
            if (!emitAtomOp(pndot->pn_right->pn_atom, JSOP_GETPROP))
                return false;

            /* Reverse the pn_left link again. */
            pnup = pndot->pn_left;
            pndot->pn_left = pndown;
            pndown = pndot;
        } while ((pndot = pnup) != nullptr);
        return true;
    }

    // The non-optimized case.
    return emitTree(pn2);
}

bool
BytecodeEmitter::emitPropIncDec(ParseNode* pn)
{
    PropertyAccess* prop = &pn->pn_kid->as<PropertyAccess>();

    bool isSuper = prop->isSuper();
    ParseNodeKind kind = pn->getKind();
    PropOpEmitter poe(this,
                      kind == ParseNodeKind::PostIncrement ? PropOpEmitter::Kind::PostIncrement
                      : kind == ParseNodeKind::PreIncrement ? PropOpEmitter::Kind::PreIncrement
                      : kind == ParseNodeKind::PostDecrement ? PropOpEmitter::Kind::PostDecrement
                      : PropOpEmitter::Kind::PreDecrement,
                      isSuper
                      ? PropOpEmitter::ObjKind::Super
                      : PropOpEmitter::ObjKind::Other);
    if (!poe.prepareForObj()) {
        return false;
    }
    if (isSuper) {
        ParseNode* base = &prop->expression();
        if (!emitGetThisForSuperBase(base)) {       // THIS
            return false;
        }
    } else {
        if (!emitPropLHS(prop)) {
            return false;                           // OBJ
        }
    }
    if (!poe.emitIncDec(prop->key().pn_atom)) {     // RESULT
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitNameIncDec(ParseNode* pn)
{
    MOZ_ASSERT(pn->pn_kid->isKind(ParseNodeKind::Name));

    ParseNodeKind kind = pn->getKind();
    NameNode* name = &pn->pn_kid->as<NameNode>();
    NameOpEmitter noe(this, name->pn_atom,
                      kind == ParseNodeKind::PostIncrement ? NameOpEmitter::Kind::PostIncrement
                      : kind == ParseNodeKind::PreIncrement ? NameOpEmitter::Kind::PreIncrement
                      : kind == ParseNodeKind::PostDecrement ? NameOpEmitter::Kind::PostDecrement
                      : NameOpEmitter::Kind::PreDecrement);
    if (!noe.emitIncDec()) {
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitElemOpBase(JSOp op)
{
    if (!emit1(op))
        return false;

    checkTypeSet(op);
    return true;
}

bool
BytecodeEmitter::emitElemObjAndKey(PropertyByValue* elem, bool isSuper, ElemOpEmitter& eoe)
{
    if (isSuper) {
        if (!eoe.prepareForObj()) {                       //
            return false;
        }
        UnaryNode* base = &elem->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {             // THIS
            return false;
        }
        if (!eoe.prepareForKey()) {                       // THIS
            return false;
        }
        if (!emitTree(&elem->key())) {                    // THIS KEY
            return false;
        }

        return true;
    }

    if (!eoe.prepareForObj()) {                           //
        return false;
    }
    if (!emitTree(&elem->expression())) {                 // OBJ
        return false;
    }
    if (!eoe.prepareForKey()) {                           // OBJ? OBJ
        return false;
    }
    if (!emitTree(&elem->key())) {                        // OBJ? OBJ KEY
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitElemIncDec(ParseNode* pn)
{
    PropertyByValue* elemExpr = &pn->pn_kid->as<PropertyByValue>();
    bool isSuper = elemExpr->isSuper();
    ParseNodeKind kind = pn->getKind();
    ElemOpEmitter eoe(this,
                      kind == ParseNodeKind::PostIncrement ? ElemOpEmitter::Kind::PostIncrement
                      : kind == ParseNodeKind::PreIncrement ? ElemOpEmitter::Kind::PreIncrement
                      : kind == ParseNodeKind::PostDecrement ? ElemOpEmitter::Kind::PostDecrement
                      : ElemOpEmitter::Kind::PreDecrement,
                      isSuper
                      ? ElemOpEmitter::ObjKind::Super
                      : ElemOpEmitter::ObjKind::Other);
    if (!emitElemObjAndKey(elemExpr, isSuper, eoe)) {     // [Super]
        //                                                // THIS KEY
        //                                                // [Other]
        //                                                // OBJ KEY
        return false;
    }
    if (!eoe.emitIncDec()) {                              // RESULT
         return false;
    }

    return true;
}

bool
BytecodeEmitter::emitCallIncDec(ParseNode* incDec)
{
    MOZ_ASSERT(incDec->isKind(ParseNodeKind::PreIncrement) ||
               incDec->isKind(ParseNodeKind::PostIncrement) ||
               incDec->isKind(ParseNodeKind::PreDecrement) ||
               incDec->isKind(ParseNodeKind::PostDecrement));

    MOZ_ASSERT(incDec->pn_kid->isKind(ParseNodeKind::Call));

    ParseNode* call = incDec->pn_kid;
    if (!emitTree(call))                                // CALLRESULT
        return false;
    if (!emit1(JSOP_POS))                               // N
        return false;

    // The increment/decrement has no side effects, so proceed to throw for
    // invalid assignment target.
    return emitUint16Operand(JSOP_THROWMSG, JSMSG_BAD_LEFTSIDE_OF_ASS);
}

bool
BytecodeEmitter::emitNumberOp(double dval)
{
    int32_t ival;
    if (NumberIsInt32(dval, &ival)) {
        if (ival == 0)
            return emit1(JSOP_ZERO);
        if (ival == 1)
            return emit1(JSOP_ONE);
        if ((int)(int8_t)ival == ival)
            return emit2(JSOP_INT8, uint8_t(int8_t(ival)));

        uint32_t u = uint32_t(ival);
        if (u < JS_BIT(16)) {
            if (!emitUint16Operand(JSOP_UINT16, u))
                return false;
        } else if (u < JS_BIT(24)) {
            ptrdiff_t off;
            if (!emitN(JSOP_UINT24, 3, &off))
                return false;
            SET_UINT24(code(off), u);
        } else {
            ptrdiff_t off;
            if (!emitN(JSOP_INT32, 4, &off))
                return false;
            SET_INT32(code(off), ival);
        }
        return true;
    }

    if (!constList.append(DoubleValue(dval)))
        return false;

    return emitIndex32(JSOP_DOUBLE, constList.length() - 1);
}

/*
 * Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047.
 * LLVM is deciding to inline this function which uses a lot of stack space
 * into emitTree which is recursive and uses relatively little stack space.
 */
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitSwitch(ParseNode* pn)
{
    ParseNode* cases = pn->pn_right;
    MOZ_ASSERT(cases->isKind(ParseNodeKind::LexicalScope) ||
               cases->isKind(ParseNodeKind::StatementList));

    // Emit code for the discriminant.
    if (!emitTree(pn->pn_left))
        return false;

    // Enter the scope before pushing the switch BreakableControl since all
    // breaks are under this scope.
    Maybe<TDZCheckCache> tdzCache;
    Maybe<EmitterScope> emitterScope;
    if (cases->isKind(ParseNodeKind::LexicalScope)) {
        if (!cases->isEmptyScope()) {
            tdzCache.emplace(this);
            emitterScope.emplace(this);
            if (!emitterScope->enterLexical(this, ScopeKind::Lexical, cases->scopeBindings()))
                return false;
        }

        // Advance |cases| to refer to the switch case list.
        cases = cases->scopeBody();

        // A switch statement may contain hoisted functions inside its
        // cases. The PNX_FUNCDEFS flag is propagated from the STATEMENTLIST
        // bodies of the cases to the case list.
        if (cases->pn_xflags & PNX_FUNCDEFS) {
            MOZ_ASSERT(emitterScope);
            for (ParseNode* caseNode = cases->pn_head; caseNode; caseNode = caseNode->pn_next) {
                if (caseNode->pn_right->pn_xflags & PNX_FUNCDEFS) {
                    if (!emitHoistedFunctionsInList(caseNode->pn_right))
                        return false;
                }
            }
        }
    }

    // After entering the scope, push the switch control.
    BreakableControl controlInfo(this, StatementKind::Switch);

    ptrdiff_t top = offset();

    // Switch bytecodes run from here till end of final case.
    uint32_t caseCount = cases->pn_count;
    if (caseCount > JS_BIT(16)) {
        parser.reportError(JSMSG_TOO_MANY_CASES);
        return false;
    }

    // Try for most optimal, fall back if not dense ints.
    JSOp switchOp = JSOP_TABLESWITCH;
    uint32_t tableLength = 0;
    int32_t low, high;
    bool hasDefault = false;
    CaseClause* firstCase = cases->pn_head ? &cases->pn_head->as<CaseClause>() : nullptr;
    if (caseCount == 0 ||
        (caseCount == 1 && (hasDefault = firstCase->isDefault())))
    {
        caseCount = 0;
        low = 0;
        high = -1;
    } else {
        Vector<jsbitmap, 128, SystemAllocPolicy> intmap;
        int32_t intmapBitLength = 0;

        low  = JSVAL_INT_MAX;
        high = JSVAL_INT_MIN;

        for (CaseClause* caseNode = firstCase; caseNode; caseNode = caseNode->next()) {
            if (caseNode->isDefault()) {
                hasDefault = true;
                caseCount--;  // one of the "cases" was the default
                continue;
            }

            if (switchOp == JSOP_CONDSWITCH)
                continue;

            MOZ_ASSERT(switchOp == JSOP_TABLESWITCH);

            ParseNode* caseValue = caseNode->caseExpression();

            if (caseValue->getKind() != ParseNodeKind::Number) {
                switchOp = JSOP_CONDSWITCH;
                continue;
            }

            int32_t i;
            if (!NumberIsInt32(caseValue->pn_dval, &i)) {
                switchOp = JSOP_CONDSWITCH;
                continue;
            }

            if (unsigned(i + int(JS_BIT(15))) >= unsigned(JS_BIT(16))) {
                switchOp = JSOP_CONDSWITCH;
                continue;
            }
            if (i < low)
                low = i;
            if (i > high)
                high = i;

            // Check for duplicates, which require a JSOP_CONDSWITCH.
            // We bias i by 65536 if it's negative, and hope that's a rare
            // case (because it requires a malloc'd bitmap).
            if (i < 0)
                i += JS_BIT(16);
            if (i >= intmapBitLength) {
                size_t newLength = (i / JS_BITMAP_NBITS) + 1;
                if (!intmap.resize(newLength))
                    return false;
                intmapBitLength = newLength * JS_BITMAP_NBITS;
            }
            if (JS_TEST_BIT(intmap, i)) {
                switchOp = JSOP_CONDSWITCH;
                continue;
            }
            JS_SET_BIT(intmap, i);
        }

        // Compute table length and select condswitch instead if overlarge or
        // more than half-sparse.
        if (switchOp == JSOP_TABLESWITCH) {
            tableLength = uint32_t(high - low + 1);
            if (tableLength >= JS_BIT(16) || tableLength > 2 * caseCount)
                switchOp = JSOP_CONDSWITCH;
        }
    }

    // The note has one or two offsets: first tells total switch code length;
    // second (if condswitch) tells offset to first JSOP_CASE.
    unsigned noteIndex;
    size_t switchSize;
    if (switchOp == JSOP_CONDSWITCH) {
        // 0 bytes of immediate for unoptimized switch.
        switchSize = 0;
        if (!newSrcNote3(SRC_CONDSWITCH, 0, 0, &noteIndex))
            return false;
    } else {
        MOZ_ASSERT(switchOp == JSOP_TABLESWITCH);

        // 3 offsets (len, low, high) before the table, 1 per entry.
        switchSize = size_t(JUMP_OFFSET_LEN * (3 + tableLength));
        if (!newSrcNote2(SRC_TABLESWITCH, 0, &noteIndex))
            return false;
    }

    // Emit switchOp followed by switchSize bytes of jump or lookup table.
    MOZ_ASSERT(top == offset());
    if (!emitN(switchOp, switchSize))
        return false;

    Vector<CaseClause*, 32, SystemAllocPolicy> table;

    JumpList condSwitchDefaultOff;
    if (switchOp == JSOP_CONDSWITCH) {
        unsigned caseNoteIndex;
        bool beforeCases = true;
        ptrdiff_t lastCaseOffset = -1;

        // The case conditions need their own TDZ cache since they might not
        // all execute.
        TDZCheckCache tdzCache(this);

        // Emit code for evaluating cases and jumping to case statements.
        for (CaseClause* caseNode = firstCase; caseNode; caseNode = caseNode->next()) {
            ParseNode* caseValue = caseNode->caseExpression();

            // If the expression is a literal, suppress line number emission so
            // that debugging works more naturally.
            if (caseValue) {
                if (!emitTree(caseValue, ValueUsage::WantValue,
                              caseValue->isLiteral() ? SUPPRESS_LINENOTE : EMIT_LINENOTE))
                {
                    return false;
                }
            }

            if (!beforeCases) {
                // prevCase is the previous JSOP_CASE's bytecode offset.
                if (!setSrcNoteOffset(caseNoteIndex, 0, offset() - lastCaseOffset))
                    return false;
            }
            if (!caseValue) {
                // This is the default clause.
                continue;
            }

            if (!newSrcNote2(SRC_NEXTCASE, 0, &caseNoteIndex))
                return false;

            // The case clauses are produced before any of the case body. The
            // JumpList is saved on the parsed tree, then later restored and
            // patched when generating the cases body.
            JumpList caseJump;
            if (!emitJump(JSOP_CASE, &caseJump))
                return false;
            caseNode->setOffset(caseJump.offset);
            lastCaseOffset = caseJump.offset;

            if (beforeCases) {
                // Switch note's second offset is to first JSOP_CASE.
                unsigned noteCount = notes().length();
                if (!setSrcNoteOffset(noteIndex, 1, lastCaseOffset - top))
                    return false;
                unsigned noteCountDelta = notes().length() - noteCount;
                if (noteCountDelta != 0)
                    caseNoteIndex += noteCountDelta;
                beforeCases = false;
            }
        }

        // If we didn't have an explicit default (which could fall in between
        // cases, preventing us from fusing this setSrcNoteOffset with the call
        // in the loop above), link the last case to the implicit default for
        // the benefit of IonBuilder.
        if (!hasDefault &&
            !beforeCases &&
            !setSrcNoteOffset(caseNoteIndex, 0, offset() - lastCaseOffset))
        {
            return false;
        }

        // Emit default even if no explicit default statement.
        if (!emitJump(JSOP_DEFAULT, &condSwitchDefaultOff))
            return false;
    } else {
        MOZ_ASSERT(switchOp == JSOP_TABLESWITCH);

        // skip default offset.
        jsbytecode* pc = code(top + JUMP_OFFSET_LEN);

        // Fill in switch bounds, which we know fit in 16-bit offsets.
        SET_JUMP_OFFSET(pc, low);
        pc += JUMP_OFFSET_LEN;
        SET_JUMP_OFFSET(pc, high);
        pc += JUMP_OFFSET_LEN;

        if (tableLength != 0) {
            if (!table.growBy(tableLength))
                return false;

            for (CaseClause* caseNode = firstCase; caseNode; caseNode = caseNode->next()) {
                if (ParseNode* caseValue = caseNode->caseExpression()) {
                    MOZ_ASSERT(caseValue->isKind(ParseNodeKind::Number));

                    int32_t i = int32_t(caseValue->pn_dval);
                    MOZ_ASSERT(double(i) == caseValue->pn_dval);

                    i -= low;
                    MOZ_ASSERT(uint32_t(i) < tableLength);
                    MOZ_ASSERT(!table[i]);
                    table[i] = caseNode;
                }
            }
        }
    }

    JumpTarget defaultOffset{ -1 };

    // Emit code for each case's statements.
    for (CaseClause* caseNode = firstCase; caseNode; caseNode = caseNode->next()) {
        if (switchOp == JSOP_CONDSWITCH && !caseNode->isDefault()) {
            // The case offset got saved in the caseNode structure after
            // emitting the JSOP_CASE jump instruction above.
            JumpList caseCond;
            caseCond.offset = caseNode->offset();
            if (!emitJumpTargetAndPatch(caseCond))
                return false;
        }

        JumpTarget here;
        if (!emitJumpTarget(&here))
            return false;
        if (caseNode->isDefault())
            defaultOffset = here;

        // If this is emitted as a TABLESWITCH, we'll need to know this case's
        // offset later when emitting the table. Store it in the node's
        // pn_offset (giving the field a different meaning vs. how we used it
        // on the immediately preceding line of code).
        caseNode->setOffset(here.offset);

        TDZCheckCache tdzCache(this);

        if (!emitTree(caseNode->statementList()))
            return false;
    }

    if (!hasDefault) {
        // If no default case, offset for default is to end of switch.
        if (!emitJumpTarget(&defaultOffset))
            return false;
    }
    MOZ_ASSERT(defaultOffset.offset != -1);

    // Set the default offset (to end of switch if no default).
    jsbytecode* pc;
    if (switchOp == JSOP_CONDSWITCH) {
        pc = nullptr;
        patchJumpsToTarget(condSwitchDefaultOff, defaultOffset);
    } else {
        MOZ_ASSERT(switchOp == JSOP_TABLESWITCH);
        pc = code(top);
        SET_JUMP_OFFSET(pc, defaultOffset.offset - top);
        pc += JUMP_OFFSET_LEN;
    }

    // Set the SRC_SWITCH note's offset operand to tell end of switch.
    if (!setSrcNoteOffset(noteIndex, 0, lastNonJumpTargetOffset() - top))
        return false;

    if (switchOp == JSOP_TABLESWITCH) {
        // Skip over the already-initialized switch bounds.
        pc += 2 * JUMP_OFFSET_LEN;

        // Fill in the jump table, if there is one.
        for (uint32_t i = 0; i < tableLength; i++) {
            CaseClause* caseNode = table[i];
            ptrdiff_t off = caseNode ? caseNode->offset() - top : 0;
            SET_JUMP_OFFSET(pc, off);
            pc += JUMP_OFFSET_LEN;
        }
    }

    // Patch breaks before leaving the scope, as all breaks are under the
    // lexical scope if it exists.
    if (!controlInfo.patchBreaks(this))
        return false;

    if (emitterScope && !emitterScope->leave(this))
        return false;

    return true;
}

bool
BytecodeEmitter::isRunOnceLambda()
{
    // The run once lambda flags set by the parser are approximate, and we look
    // at properties of the function itself before deciding to emit a function
    // as a run once lambda.

    if (!(parent && parent->emittingRunOnceLambda) &&
        (emitterMode != LazyFunction || !lazyScript->treatAsRunOnce()))
    {
        return false;
    }

    FunctionBox* funbox = sc->asFunctionBox();
    return !funbox->argumentsHasLocalBinding() &&
           !funbox->isStarGenerator() &&
           !funbox->isLegacyGenerator() &&
           !funbox->isAsync() &&
           !funbox->function()->explicitName();
}

bool
BytecodeEmitter::emitYieldOp(JSOp op)
{
    if (op == JSOP_FINALYIELDRVAL)
        return emit1(JSOP_FINALYIELDRVAL);

    MOZ_ASSERT(op == JSOP_INITIALYIELD || op == JSOP_YIELD || op == JSOP_AWAIT);

    ptrdiff_t off;
    if (!emitN(op, 3, &off))
        return false;

    uint32_t yieldAndAwaitIndex = yieldAndAwaitOffsetList.length();
    if (yieldAndAwaitIndex >= JS_BIT(24)) {
        reportError(nullptr, JSMSG_TOO_MANY_YIELDS);
        return false;
    }

    if (op == JSOP_AWAIT)
        yieldAndAwaitOffsetList.numAwaits++;
    else
        yieldAndAwaitOffsetList.numYields++;

    SET_UINT24(code(off), yieldAndAwaitIndex);

    if (!yieldAndAwaitOffsetList.append(offset()))
        return false;

    return emit1(JSOP_DEBUGAFTERYIELD);
}

bool
BytecodeEmitter::emitSetThis(ParseNode* pn)
{
    // ParseNodeKind::SetThis is used to update |this| after a super() call
    // in a derived class constructor.

    MOZ_ASSERT(pn->isKind(ParseNodeKind::SetThis));
    MOZ_ASSERT(pn->pn_left->isKind(ParseNodeKind::Name));

    RootedAtom name(cx, pn->pn_left->name());

    // The 'this' binding is not lexical, but due to super() semantics this
    // initialization needs to be treated as a lexical one.
    NameLocation loc = lookupName(name);
    NameLocation lexicalLoc;
    if (loc.kind() == NameLocation::Kind::FrameSlot) {
        lexicalLoc = NameLocation::FrameSlot(BindingKind::Let, loc.frameSlot());
    } else if (loc.kind() == NameLocation::Kind::EnvironmentCoordinate) {
        EnvironmentCoordinate coord = loc.environmentCoordinate();
        uint8_t hops = AssertedCast<uint8_t>(coord.hops());
        lexicalLoc = NameLocation::EnvironmentCoordinate(BindingKind::Let, hops, coord.slot());
    } else {
        MOZ_ASSERT(loc.kind() == NameLocation::Kind::Dynamic);
        lexicalLoc = loc;
    }

    NameOpEmitter noe(this, name, lexicalLoc, NameOpEmitter::Kind::Initialize);
    if (!noe.prepareForRhs()) {                           //
        return false;
    }

    // Emit the new |this| value.
    if (!emitTree(pn->pn_right))                          // NEWTHIS
        return false;

    // Get the original |this| and throw if we already initialized
    // it. Do *not* use the NameLocation argument, as that's the special
    // lexical location below to deal with super() semantics.
    if (!emitGetName(name)) {                             // NEWTHIS THIS
        return false;
    }
    if (!emit1(JSOP_CHECKTHISREINIT)) {                   // NEWTHIS THIS
        return false;
    }
    if (!emit1(JSOP_POP)) {                               // NEWTHIS
        return false;
    }
    if (!noe.emitAssignment()) {                          // NEWTHIS
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitScript(ParseNode* body)
{
    AutoFrontendTraceLog traceLog(cx, TraceLogger_BytecodeEmission, tokenStream(), body);

    TDZCheckCache tdzCache(this);
    EmitterScope emitterScope(this);
    if (sc->isGlobalContext()) {
        switchToPrologue();
        if (!emitterScope.enterGlobal(this, sc->asGlobalContext()))
            return false;
        switchToMain();
    } else if (sc->isEvalContext()) {
        switchToPrologue();
        if (!emitterScope.enterEval(this, sc->asEvalContext()))
            return false;
        switchToMain();
    } else {
        MOZ_ASSERT(sc->isModuleContext());
        if (!emitterScope.enterModule(this, sc->asModuleContext()))
            return false;
    }

    setFunctionBodyEndPos(body->pn_pos);

    if (sc->isEvalContext() && !sc->strict() &&
        body->isKind(ParseNodeKind::LexicalScope) && !body->isEmptyScope())
    {
        // Sloppy eval scripts may need to emit DEFFUNs in the prologue. If there is
        // an immediately enclosed lexical scope, we need to enter the lexical
        // scope in the prologue for the DEFFUNs to pick up the right
        // environment chain.
        EmitterScope lexicalEmitterScope(this);

        switchToPrologue();
        if (!lexicalEmitterScope.enterLexical(this, ScopeKind::Lexical, body->scopeBindings()))
            return false;
        switchToMain();

        if (!emitLexicalScopeBody(body->scopeBody()))
            return false;

        if (!lexicalEmitterScope.leave(this))
            return false;
    } else {
        if (!emitTree(body))
            return false;
    }

    if (!updateSourceCoordNotes(body->pn_pos.end))
        return false;

    if (!emit1(JSOP_RETRVAL))
        return false;

    if (!emitterScope.leave(this))
        return false;

    if (!JSScript::fullyInitFromEmitter(cx, script, this))
        return false;

    // URL and source map information must be set before firing
    // Debugger::onNewScript.
    if (!maybeSetDisplayURL() || !maybeSetSourceMap())
        return false;

    tellDebuggerAboutCompiledScript(cx);

    return true;
}

bool
BytecodeEmitter::emitFunctionScript(ParseNode* body)
{
    FunctionBox* funbox = sc->asFunctionBox();
    AutoFrontendTraceLog traceLog(cx, TraceLogger_BytecodeEmission, tokenStream(), funbox);

    // The ordering of these EmitterScopes is important. The named lambda
    // scope needs to enclose the function scope needs to enclose the extra
    // var scope.

    Maybe<EmitterScope> namedLambdaEmitterScope;
    if (funbox->namedLambdaBindings()) {
        namedLambdaEmitterScope.emplace(this);
        if (!namedLambdaEmitterScope->enterNamedLambda(this, funbox))
            return false;
    }

    /*
     * Emit a prologue for run-once scripts which will deoptimize JIT code
     * if the script ends up running multiple times via foo.caller related
     * shenanigans.
     *
     * Also mark the script so that initializers created within it may be
     * given more precise types.
     */
    if (isRunOnceLambda()) {
        script->setTreatAsRunOnce();
        MOZ_ASSERT(!script->hasRunOnce());

        switchToPrologue();
        if (!emit1(JSOP_RUNONCE))
            return false;
        switchToMain();
    }

    setFunctionBodyEndPos(body->pn_pos);
    if (!emitTree(body))
        return false;

    if (!updateSourceCoordNotes(body->pn_pos.end))
        return false;

    // Always end the script with a JSOP_RETRVAL. Some other parts of the
    // codebase depend on this opcode,
    // e.g. InterpreterRegs::setToEndOfScript.
    if (!emit1(JSOP_RETRVAL))
        return false;

    if (namedLambdaEmitterScope) {
        if (!namedLambdaEmitterScope->leave(this))
            return false;
        namedLambdaEmitterScope.reset();
    }

    if (!JSScript::fullyInitFromEmitter(cx, script, this))
        return false;

    // URL and source map information must be set before firing
    // Debugger::onNewScript. Only top-level functions need this, as compiling
    // the outer scripts of nested functions already processed the source.
    if (emitterMode != LazyFunction && !parent) {
        if (!maybeSetDisplayURL() || !maybeSetSourceMap())
            return false;

        tellDebuggerAboutCompiledScript(cx);
    }

    return true;
}

bool
BytecodeEmitter::emitDestructuringLHSRef(ParseNode* target, size_t* emitted)
{
    *emitted = 0;

    if (target->isKind(ParseNodeKind::Spread))
        target = target->pn_kid;
    else if (target->isKind(ParseNodeKind::Assign))
        target = target->pn_left;

    // No need to recur into ParseNodeKind::Array and
    // ParseNodeKind::Object subpatterns here, since
    // emitSetOrInitializeDestructuring does the recursion when
    // setting or initializing value.  Getting reference doesn't recur.
    if (target->isKind(ParseNodeKind::Name) ||
        target->isKind(ParseNodeKind::Array) ||
        target->isKind(ParseNodeKind::Object))
    {
        return true;
    }

#ifdef DEBUG
    int depth = stackDepth;
#endif

    switch (target->getKind()) {
      case ParseNodeKind::Dot: {
        PropertyAccess* prop = &target->as<PropertyAccess>();
        bool isSuper = prop->isSuper();
        PropOpEmitter poe(this,
                          PropOpEmitter::Kind::SimpleAssignment,
                          isSuper
                          ? PropOpEmitter::ObjKind::Super
                          : PropOpEmitter::ObjKind::Other);
        if (!poe.prepareForObj()) {
            return false;
        }
        if (isSuper) {
            UnaryNode* base = &prop->expression().as<UnaryNode>();
            if (!emitGetThisForSuperBase(base)) {         // THIS SUPERBASE
                return false;
            }
            // SUPERBASE is pushed onto THIS in poe.prepareForRhs below.
            *emitted = 2;
        } else {
            if (!emitTree(&prop->expression())) {             // OBJ
                return false;
            }
            *emitted = 1;
        }
        if (!poe.prepareForRhs()) {                       // [Super]
            //                                            // THIS SUPERBASE
            //                                            // [Other]
            //                                            // OBJ
            return false;
        }
        break;
      }

      case ParseNodeKind::Elem: {
        PropertyByValue* elem = &target->as<PropertyByValue>();
        bool isSuper = elem->isSuper();
        ElemOpEmitter eoe(this,
                          ElemOpEmitter::Kind::SimpleAssignment,
                          isSuper
                          ? ElemOpEmitter::ObjKind::Super
                          : ElemOpEmitter::ObjKind::Other);
        if (!emitElemObjAndKey(elem, isSuper, eoe)) {     // [Super]
            //                                            // THIS KEY
            //                                            // [Other]
            //                                            // OBJ KEY
            return false;
        }
        if (isSuper) {
            // SUPERBASE is pushed onto KEY in eoe.prepareForRhs below.
            *emitted = 3;
        } else {
            *emitted = 2;
        }
        if (!eoe.prepareForRhs()) {                       // [Super]
            //                                            // THIS KEY SUPERBASE
            //                                            // [Other]
            //                                            // OBJ KEY
            return false;
        }
        break;
      }

      case ParseNodeKind::Call:
        MOZ_ASSERT_UNREACHABLE("Parser::reportIfNotValidSimpleAssignmentTarget "
                               "rejects function calls as assignment "
                               "targets in destructuring assignments");
        break;

      default:
        MOZ_CRASH("emitDestructuringLHSRef: bad lhs kind");
    }

    MOZ_ASSERT(stackDepth == depth + int(*emitted));

    return true;
}

bool
BytecodeEmitter::emitSetOrInitializeDestructuring(ParseNode* target, DestructuringFlavor flav)
{
    // Now emit the lvalue opcode sequence. If the lvalue is a nested
    // destructuring initialiser-form, call ourselves to handle it, then pop
    // the matched value. Otherwise emit an lvalue bytecode sequence followed
    // by an assignment op.
    if (target->isKind(ParseNodeKind::Spread))
        target = target->pn_kid;
    else if (target->isKind(ParseNodeKind::Assign))
        target = target->pn_left;
    if (target->isKind(ParseNodeKind::Array) || target->isKind(ParseNodeKind::Object)) {
        if (!emitDestructuringOps(target, flav))
            return false;
        // Per its post-condition, emitDestructuringOps has left the
        // to-be-destructured value on top of the stack.
        if (!emit1(JSOP_POP))
            return false;
    } else {
        switch (target->getKind()) {
          case ParseNodeKind::Name: {
            RootedAtom name(cx, target->name());
            NameLocation loc;
            NameOpEmitter::Kind kind;
            switch (flav) {
              case DestructuringDeclaration:
                loc = lookupName(name);
                kind = NameOpEmitter::Kind::Initialize;
                break;

              case DestructuringFormalParameterInVarScope: {
                // If there's an parameter expression var scope, the
                // destructuring declaration needs to initialize the name in
                // the function scope. The innermost scope is the var scope,
                // and its enclosing scope is the function scope.
                EmitterScope* funScope = innermostEmitterScope()->enclosingInFrame();
                loc = *locationOfNameBoundInScope(name, funScope);
                kind = NameOpEmitter::Kind::Initialize;
                break;
              }

              case DestructuringAssignment:
                loc = lookupName(name);
                kind = NameOpEmitter::Kind::SimpleAssignment;
                break;
            }

            NameOpEmitter noe(this, name, loc, kind);
            if (!noe.prepareForRhs()) {                   // V ENV?
                return false;
            }
            if (noe.emittedBindOp()) {
                // This is like ordinary assignment, but with one difference.
                //
                // In `a = b`, we first determine a binding for `a` (using
                // JSOP_BINDNAME or JSOP_BINDGNAME), then we evaluate `b`, then
                // a JSOP_SETNAME instruction.
                //
                // In `[a] = [b]`, per spec, `b` is evaluated first, then we
                // determine a binding for `a`. Then we need to do assignment--
                // but the operands are on the stack in the wrong order for
                // JSOP_SETPROP, so we have to add a JSOP_SWAP.
                //
                // In the cases where we are emitting a name op, emit a swap
                // because of this.
                if (!emit1(JSOP_SWAP)) {                  // ENV V
                    return false;
                }
            } else {
                // In cases of emitting a frame slot or environment slot,
                // nothing needs be done.
            }
            if (!noe.emitAssignment()) {                  // V
                return false;
            }

            break;
          }

          case ParseNodeKind::Dot: {
            // The reference is already pushed by emitDestructuringLHSRef.
            //                                            // [Super]
            //                                            // THIS SUPERBASE VAL
            //                                            // [Other]
            //                                            // OBJ VAL
            PropertyAccess* prop = &target->as<PropertyAccess>();
            bool isSuper = prop->isSuper();
            PropOpEmitter poe(this,
                              PropOpEmitter::Kind::SimpleAssignment,
                              isSuper
                              ? PropOpEmitter::ObjKind::Super
                              : PropOpEmitter::ObjKind::Other);
            if (!poe.skipObjAndRhs()) {
                return false;
            }
            if (!poe.emitAssignment(prop->key().pn_atom)) {
                return false;                             // VAL
            }
            break;
          }

          case ParseNodeKind::Elem: {
            // The reference is already pushed by emitDestructuringLHSRef.
            //                                            // [Super]
            //                                            // THIS KEY SUPERBASE VAL
            //                                            // [Other]
            //                                            // OBJ KEY VAL
            PropertyByValue* elem = &target->as<PropertyByValue>();
            bool isSuper = elem->isSuper();
            ElemOpEmitter eoe(this,
                              ElemOpEmitter::Kind::SimpleAssignment,
                              isSuper
                              ? ElemOpEmitter::ObjKind::Super
                              : ElemOpEmitter::ObjKind::Other);
            if (!eoe.skipObjAndKeyAndRhs()) {
                return false;
            }
            if (!eoe.emitAssignment()) {                  // VAL
                return false;
            }
            break;
          }

          case ParseNodeKind::Call:
            MOZ_ASSERT_UNREACHABLE("Parser::reportIfNotValidSimpleAssignmentTarget "
                                   "rejects function calls as assignment "
                                   "targets in destructuring assignments");
            break;

          default:
            MOZ_CRASH("emitSetOrInitializeDestructuring: bad lhs kind");
        }

        // Pop the assigned value.
        if (!emit1(JSOP_POP)) {                           // !STACK EMPTY!
            return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitIteratorNext(ParseNode* pn, IteratorKind iterKind /* = IteratorKind::Sync */,
                                  bool allowSelfHosted /* = false */)
{
    MOZ_ASSERT(allowSelfHosted || emitterMode != BytecodeEmitter::SelfHosting,
               ".next() iteration is prohibited in self-hosted code because it "
               "can run user-modifiable iteration code");

    if (!emit1(JSOP_DUP))                                 // ... ITER ITER
        return false;
    if (!emitAtomOp(cx->names().next, JSOP_CALLPROP))     // ... ITER NEXT
        return false;
    if (!emit1(JSOP_SWAP))                                // ... NEXT ITER
        return false;
    if (!emitCall(JSOP_CALL, 0, pn))                      // ... RESULT
        return false;

    if (iterKind == IteratorKind::Async) {
        if (!emitAwaitInInnermostScope())                 // ... RESULT
            return false;
    }

    if (!emitCheckIsObj(CheckIsObjectKind::IteratorNext)) // ... RESULT
        return false;
    checkTypeSet(JSOP_CALL);
    return true;
}

bool
BytecodeEmitter::emitPushNotUndefinedOrNull()
{
    MOZ_ASSERT(this->stackDepth > 0);                     // V

    if (!emit1(JSOP_DUP))                                 // V V
        return false;
    if (!emit1(JSOP_UNDEFINED))                           // V V UNDEFINED
        return false;
    if (!emit1(JSOP_STRICTNE))                            // V ?NEQL
        return false;

    JumpList undefinedOrNullJump;
    if (!emitJump(JSOP_AND, &undefinedOrNullJump))        // V ?NEQL
        return false;

    if (!emit1(JSOP_POP))                                 // V
        return false;
    if (!emit1(JSOP_DUP))                                 // V V
        return false;
    if (!emit1(JSOP_NULL))                                // V V NULL
        return false;
    if (!emit1(JSOP_STRICTNE))                            // V ?NEQL
        return false;

    if (!emitJumpTargetAndPatch(undefinedOrNullJump))     // V NOT-UNDEF-OR-NULL
        return false;

    return true;
}

bool
BytecodeEmitter::emitIteratorCloseInScope(EmitterScope& currentScope,
                                          IteratorKind iterKind /* = IteratorKind::Sync */,
                                          CompletionKind completionKind /* = CompletionKind::Normal */,
                                          bool allowSelfHosted /* = false */)
{
    MOZ_ASSERT(allowSelfHosted || emitterMode != BytecodeEmitter::SelfHosting,
               ".close() on iterators is prohibited in self-hosted code because it "
               "can run user-modifiable iteration code");

    // Generate inline logic corresponding to IteratorClose (ES2021 7.4.6) and
    // AsyncIteratorClose (ES2021 7.4.7). Steps numbers apply to both operations.
    //
    // Callers need to ensure that the iterator object is at the top of the
    // stack.

    // For non-Throw completions, we emit the equivalent of:
    //
    // var returnMethod = GetMethod(iterator, "return");
    // if (returnMethod !== undefined) {
    //   var innerResult = [Await] Call(returnMethod, iterator);
    //   CheckIsObj(innerResult);
    // }
    //
    // Whereas for Throw completions, we emit:
    //
    // try {
    //   var returnMethod = GetMethod(iterator, "return");
    //   if (returnMethod !== undefined) {
    //     [Await] Call(returnMethod, iterator);
    //   }
    // } catch {}

    Maybe<TryEmitter> tryCatch;

    if (completionKind == CompletionKind::Throw) {
        tryCatch.emplace(this, TryEmitter::Kind::TryCatch,
                         TryEmitter::ControlKind::NonSyntactic);

        if (!tryCatch->emitTry()) {                       // ... ITER
            return false;
        }
    }

    if (!emit1(JSOP_DUP))                                 // ... ITER ITER
        return false;

    // Steps 1-2 are assertions, step 3 is implicit.

    // Step 4.
    //
    // Get the "return" method.
    if (!emitAtomOp(cx->names().return_, JSOP_CALLPROP))  // ... ITER RET
        return false;

    // Step 5.
    //
    // Do nothing if "return" is undefined or null.
    InternalIfEmitter ifReturnMethodIsDefined(this);
    if (!emitPushNotUndefinedOrNull())                    // ... ITER RET NOT-UNDEF-OR-NULL
        return false;

    if (!ifReturnMethodIsDefined.emitThenElse())          // ... ITER RET
        return false;

    // Steps 5.c, 7.
    //
    // Call the "return" method.
    if (!emit1(JSOP_SWAP))                                // ... RET ITER
        return false;

    if (!emitCall(JSOP_CALL, 0))                          // ... RESULT
        return false;
    checkTypeSet(JSOP_CALL);

    // 7.4.7 AsyncIteratorClose, step 5.d.
    if (iterKind == IteratorKind::Async) {
        if (completionKind != CompletionKind::Throw) {
            // Await clobbers rval, so save the current rval.
            if (!emit1(JSOP_GETRVAL))                     // ... RESULT RVAL
                return false;
            if (!emit1(JSOP_SWAP))                        // ... RVAL RESULT
                return false;
        }
        if (!emitAwaitInScope(currentScope))              // ... RVAL? RESULT
            return false;

        if (completionKind != CompletionKind::Throw) {
            if (!emit1(JSOP_SWAP))                        // ... RESULT RVAL
                return false;
            if (!emit1(JSOP_SETRVAL))                     // ... RESULT
                return false;
        }
    }

    // Step 6 (Handled in caller).

    // Step 8.
    if (completionKind != CompletionKind::Throw) {
      // Check that the "return" result is an object.
        if (!emitCheckIsObj(CheckIsObjectKind::IteratorReturn)) { // ... RESULT
            return false;
        }
    }

    if (!ifReturnMethodIsDefined.emitElse())              // ... ITER RET
        return false;

    if (!emit1(JSOP_POP))                                 // ... ITER
        return false;

    if (!ifReturnMethodIsDefined.emitEnd())
        return false;

    if (completionKind == CompletionKind::Throw) {        // ... ITER EXC
        if (!tryCatch->emitCatch()) {
            return false;
        }

        // Just ignore the exception thrown by call and await.
        if (!emit1(JSOP_POP)) {                           // ... ITER
            return false;
        }

        if (!tryCatch->emitEnd()) {                       // ... ITER
            return false;
        }
    }

    // Step 9 (Handled in caller).

    return emit1(JSOP_POP);                               // ...
}

template <typename InnerEmitter>
bool
BytecodeEmitter::wrapWithDestructuringIteratorCloseTryNote(int32_t iterDepth, InnerEmitter emitter)
{
    MOZ_ASSERT(this->stackDepth >= iterDepth);

    // Pad a nop at the beginning of the bytecode covered by the trynote so
    // that when unwinding environments, we may unwind to the scope
    // corresponding to the pc *before* the start, in case the first bytecode
    // emitted by |emitter| is the start of an inner scope. See comment above
    // UnwindEnvironmentToTryPc.
    if (!emit1(JSOP_TRY_DESTRUCTURING_ITERCLOSE))
        return false;

    ptrdiff_t start = offset();
    if (!emitter(this))
        return false;
    ptrdiff_t end = offset();
    if (start != end)
        return tryNoteList.append(JSTRY_DESTRUCTURING_ITERCLOSE, iterDepth, start, end);
    return true;
}

bool
BytecodeEmitter::emitDefault(ParseNode* defaultExpr, ParseNode* pattern)
{
    if (!emit1(JSOP_DUP))                                 // VALUE VALUE
        return false;
    if (!emit1(JSOP_UNDEFINED))                           // VALUE VALUE UNDEFINED
        return false;
    if (!emit1(JSOP_STRICTEQ))                            // VALUE EQL?
        return false;
    // Emit source note to enable ion compilation.
    if (!newSrcNote(SRC_IF))
        return false;
    JumpList jump;
    if (!emitJump(JSOP_IFEQ, &jump))                      // VALUE
        return false;
    if (!emit1(JSOP_POP))                                 // .
        return false;
    if (!emitInitializerInBranch(defaultExpr, pattern))   // DEFAULTVALUE
        return false;
    if (!emitJumpTargetAndPatch(jump))
        return false;
    return true;
}

bool
BytecodeEmitter::emitAnonymousFunctionWithName(ParseNode* node, HandleAtom name)
{
  MOZ_ASSERT(node->isDirectRHSAnonFunction());

  if (node->isKind(ParseNodeKind::Function)) {
    if (!emitTree(node)) {
      return false;
    }

    // Function doesn't have 'name' property at this point.
    // Set function's name at compile time.
    return setFunName(node->pn_funbox->function(), name);
  }

  MOZ_ASSERT(node->is<ClassNode>());

  return emitClass(node, ClassNameKind::InferredName, name);
}

bool
BytecodeEmitter::emitAnonymousFunctionWithComputedName(ParseNode* node,
  FunctionPrefixKind prefixKind)
{
  MOZ_ASSERT(node->isDirectRHSAnonFunction());

  if (node->isKind(ParseNodeKind::Function)) {
    if (!emitTree(node)) {
      //            [stack] # !isAsync || !needsHomeObject
      //            [stack] NAME FUN
      //            [stack] # isAsync && needsHomeObject
      //            [stack] NAME UNWRAPPED WRAPPED
      return false;
    }
    unsigned depth = 1;
    FunctionBox* funbox = node->pn_funbox;
    if (funbox->isAsync() && funbox->needsHomeObject()) {
      depth = 2;
    }
    if (!emitDupAt(depth)) {
      //            [stack] # !isAsync || !needsHomeObject
      //            [stack] NAME FUN NAME
      //            [stack] # isAsync && needsHomeObject
      //            [stack] NAME UNWRAPPED WRAPPED NAME
      return false;
    }
    if (!emit2(JSOP_SETFUNNAME, uint8_t(prefixKind))) {
      //            [stack] # !isAsync || !needsHomeObject
      //            [stack] NAME FUN
      //            [stack] # isAsync && needsHomeObject
      //            [stack] NAME UNWRAPPED WRAPPED
      return false;
    }
    return true;
  }

  MOZ_ASSERT(node->is<ClassNode>());
  MOZ_ASSERT(prefixKind == FunctionPrefixKind::None);

  return emitClass(node, ClassNameKind::ComputedName);
}

bool
BytecodeEmitter::setFunName(JSFunction* fun, JSAtom* name)
{
    // The inferred name may already be set if this function is an interpreted
    // lazy function and we OOM'ed after we set the inferred name the first
    // time.
    if (fun->hasInferredName()) {
        MOZ_ASSERT(fun->isInterpretedLazy());
        MOZ_ASSERT(fun->inferredName() == name);

        return true;
    }

    fun->setInferredName(name);
    return true;
}

bool
BytecodeEmitter::emitInitializer(ParseNode* initializer, ParseNode* pattern)
{
    if (initializer->isDirectRHSAnonFunction()) {
        MOZ_ASSERT(!pattern->isInParens());
        RootedAtom name(cx, pattern->name());
        if (!emitAnonymousFunctionWithName(initializer, name)) {
            return false;
        }
    } else {
        if (!emitTree(initializer)) {
            return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitInitializerInBranch(ParseNode* initializer, ParseNode* pattern)
{
    TDZCheckCache tdzCache(this);
    return emitInitializer(initializer, pattern);
}

bool
BytecodeEmitter::emitDestructuringOpsArray(ParseNode* pattern, DestructuringFlavor flav)
{
    MOZ_ASSERT(pattern->isKind(ParseNodeKind::Array));
    MOZ_ASSERT(pattern->isArity(PN_LIST));
    MOZ_ASSERT(this->stackDepth != 0);

    // Here's pseudo code for |let [a, b, , c=y, ...d] = x;|
    //
    // Lines that are annotated "covered by trynote" mean that upon throwing
    // an exception, IteratorClose is called on iter only if done is false.
    //
    //   let x, y;
    //   let a, b, c, d;
    //   let iter, lref, result, done, value; // stack values
    //
    //   iter = x[Symbol.iterator]();
    //
    //   // ==== emitted by loop for a ====
    //   lref = GetReference(a);              // covered by trynote
    //
    //   result = iter.next();
    //   done = result.done;
    //
    //   if (done)
    //     value = undefined;
    //   else
    //     value = result.value;
    //
    //   SetOrInitialize(lref, value);        // covered by trynote
    //
    //   // ==== emitted by loop for b ====
    //   lref = GetReference(b);              // covered by trynote
    //
    //   if (done) {
    //     value = undefined;
    //   } else {
    //     result = iter.next();
    //     done = result.done;
    //     if (done)
    //       value = undefined;
    //     else
    //       value = result.value;
    //   }
    //
    //   SetOrInitialize(lref, value);        // covered by trynote
    //
    //   // ==== emitted by loop for elision ====
    //   if (done) {
    //     value = undefined;
    //   } else {
    //     result = iter.next();
    //     done = result.done;
    //     if (done)
    //       value = undefined;
    //     else
    //       value = result.value;
    //   }
    //
    //   // ==== emitted by loop for c ====
    //   lref = GetReference(c);              // covered by trynote
    //
    //   if (done) {
    //     value = undefined;
    //   } else {
    //     result = iter.next();
    //     done = result.done;
    //     if (done)
    //       value = undefined;
    //     else
    //       value = result.value;
    //   }
    //
    //   if (value === undefined)
    //     value = y;                         // covered by trynote
    //
    //   SetOrInitialize(lref, value);        // covered by trynote
    //
    //   // ==== emitted by loop for d ====
    //   lref = GetReference(d);              // covered by trynote
    //
    //   if (done)
    //     value = [];
    //   else
    //     value = [...iter];
    //
    //   SetOrInitialize(lref, value);        // covered by trynote
    //
    //   // === emitted after loop ===
    //   if (!done)
    //      IteratorClose(iter);

    // Use an iterator to destructure the RHS, instead of index lookup. We
    // must leave the *original* value on the stack.
    if (!emit1(JSOP_DUP))                                         // ... OBJ OBJ
        return false;
    if (!emitIterator())                                          // ... OBJ ITER
        return false;

    // For an empty pattern [], call IteratorClose unconditionally. Nothing
    // else needs to be done.
    if (!pattern->pn_head)
        return emitIteratorCloseInInnermostScope();               // ... OBJ

    // Push an initial FALSE value for DONE.
    if (!emit1(JSOP_FALSE))                                       // ... OBJ ITER FALSE
        return false;

    // JSTRY_DESTRUCTURING_ITERCLOSE expects the iterator and the done value
    // to be the second to top and the top of the stack, respectively.
    // IteratorClose is called upon exception only if done is false.
    int32_t tryNoteDepth = stackDepth;

    for (ParseNode* member = pattern->pn_head; member; member = member->pn_next) {
        bool isFirst = member == pattern->pn_head;
        DebugOnly<bool> hasNext = !!member->pn_next;

        size_t emitted = 0;

        // Spec requires LHS reference to be evaluated first.
        ParseNode* lhsPattern = member;
        if (lhsPattern->isKind(ParseNodeKind::Assign))
            lhsPattern = lhsPattern->pn_left;

        bool isElision = lhsPattern->isKind(ParseNodeKind::Elision);
        if (!isElision) {
            auto emitLHSRef = [lhsPattern, &emitted](BytecodeEmitter* bce) {
                return bce->emitDestructuringLHSRef(lhsPattern, &emitted); // ... OBJ ITER DONE *LREF
            };
            if (!wrapWithDestructuringIteratorCloseTryNote(tryNoteDepth, emitLHSRef))
                return false;
        }

        // Pick the DONE value to the top of the stack.
        if (emitted) {
            if (!emitPickN(emitted))                       // ... OBJ ITER *LREF DONE
                return false;
        }

        if (isFirst) {
            // If this element is the first, DONE is always FALSE, so pop it.
            //
            // Non-first elements should emit if-else depending on the
            // member pattern, below.
            if (!emit1(JSOP_POP))                                 // ... OBJ ITER *LREF
                return false;
        }

        if (member->isKind(ParseNodeKind::Spread)) {
            InternalIfEmitter ifThenElse(this);
            if (!isFirst) {
                // If spread is not the first element of the pattern,
                // iterator can already be completed.
                                                                  // ... OBJ ITER *LREF DONE
                if (!ifThenElse.emitThenElse())                   // ... OBJ ITER *LREF
                    return false;

                if (!emitUint32Operand(JSOP_NEWARRAY, 0))         // ... OBJ ITER *LREF ARRAY
                    return false;
                if (!ifThenElse.emitElse())                       // ... OBJ ITER *LREF
                    return false;
            }

            // If iterator is not completed, create a new array with the rest
            // of the iterator.
            if (!emitDupAt(emitted))                              // ... OBJ ITER *LREF ITER
                return false;
            if (!emitUint32Operand(JSOP_NEWARRAY, 0))             // ... OBJ ITER *LREF ITER ARRAY
                return false;
            if (!emitNumberOp(0))                                 // ... OBJ ITER *LREF ITER ARRAY INDEX
                return false;
            if (!emitSpread())                                    // ... OBJ ITER *LREF ARRAY INDEX
                return false;
            if (!emit1(JSOP_POP))                                 // ... OBJ ITER *LREF ARRAY
                return false;

            if (!isFirst) {
                if (!ifThenElse.emitEnd())
                    return false;
                MOZ_ASSERT(ifThenElse.pushed() == 1);
            }

            // At this point the iterator is done. Unpick a TRUE value for DONE above ITER.
            if (!emit1(JSOP_TRUE))                                // ... OBJ ITER *LREF ARRAY TRUE
                return false;
            if (!emit2(JSOP_UNPICK, emitted + 1))                 // ... OBJ ITER TRUE *LREF ARRAY
                return false;

            auto emitAssignment = [member, flav](BytecodeEmitter* bce) {
                return bce->emitSetOrInitializeDestructuring(member, flav); // ... OBJ ITER TRUE
            };
            if (!wrapWithDestructuringIteratorCloseTryNote(tryNoteDepth, emitAssignment))
                return false;

            MOZ_ASSERT(!hasNext);
            break;
        }

        ParseNode* pndefault = nullptr;
        if (member->isKind(ParseNodeKind::Assign))
            pndefault = member->pn_right;

        MOZ_ASSERT(!member->isKind(ParseNodeKind::Spread));

        InternalIfEmitter ifAlreadyDone(this);
        if (!isFirst) {
                                                                  // ... OBJ ITER *LREF DONE
            if (!ifAlreadyDone.emitThenElse())                    // ... OBJ ITER *LREF
                return false;

            if (!emit1(JSOP_UNDEFINED))                           // ... OBJ ITER *LREF UNDEF
                return false;
            if (!emit1(JSOP_NOP_DESTRUCTURING))                   // ... OBJ ITER *LREF UNDEF
                return false;

            // The iterator is done. Unpick a TRUE value for DONE above ITER.
            if (!emit1(JSOP_TRUE))                                // ... OBJ ITER *LREF UNDEF TRUE
                return false;
            if (!emit2(JSOP_UNPICK, emitted + 1))                 // ... OBJ ITER TRUE *LREF UNDEF
                return false;

            if (!ifAlreadyDone.emitElse())                        // ... OBJ ITER *LREF
                return false;
        }

        if (!emitDupAt(emitted))                                  // ... OBJ ITER *LREF ITER
            return false;
        if (!emitIteratorNext(pattern))                           // ... OBJ ITER *LREF RESULT
            return false;
        if (!emit1(JSOP_DUP))                                     // ... OBJ ITER *LREF RESULT RESULT
            return false;
        if (!emitAtomOp(cx->names().done, JSOP_GETPROP))          // ... OBJ ITER *LREF RESULT DONE
            return false;

        if (!emit1(JSOP_DUP))                                     // ... OBJ ITER *LREF RESULT DONE DONE
            return false;
        if (!emit2(JSOP_UNPICK, emitted + 2))                     // ... OBJ ITER DONE *LREF RESULT DONE
            return false;

        InternalIfEmitter ifDone(this);
        if (!ifDone.emitThenElse())                               // ... OBJ ITER DONE *LREF RESULT
            return false;

        if (!emit1(JSOP_POP))                                     // ... OBJ ITER DONE *LREF
            return false;
        if (!emit1(JSOP_UNDEFINED))                               // ... OBJ ITER DONE *LREF UNDEF
            return false;
        if (!emit1(JSOP_NOP_DESTRUCTURING))                       // ... OBJ ITER DONE *LREF UNDEF
            return false;

        if (!ifDone.emitElse())                                   // ... OBJ ITER DONE *LREF RESULT
            return false;

        if (!emitAtomOp(cx->names().value, JSOP_GETPROP))         // ... OBJ ITER DONE *LREF VALUE
            return false;

        if (!ifDone.emitEnd())
            return false;
        MOZ_ASSERT(ifDone.pushed() == 0);

        if (!isFirst) {
            if (!ifAlreadyDone.emitEnd())
                return false;
            MOZ_ASSERT(ifAlreadyDone.pushed() == 2);
        }

        if (pndefault) {
            auto emitDefault = [pndefault, lhsPattern](BytecodeEmitter* bce) {
                return bce->emitDefault(pndefault, lhsPattern);    // ... OBJ ITER DONE *LREF VALUE
            };

            if (!wrapWithDestructuringIteratorCloseTryNote(tryNoteDepth, emitDefault))
                return false;
        }

        if (!isElision) {
            auto emitAssignment = [lhsPattern, flav](BytecodeEmitter* bce) {
                return bce->emitSetOrInitializeDestructuring(lhsPattern, flav); // ... OBJ ITER DONE
            };

            if (!wrapWithDestructuringIteratorCloseTryNote(tryNoteDepth, emitAssignment))
                return false;
        } else {
            if (!emit1(JSOP_POP))                                 // ... OBJ ITER DONE
                return false;
        }
    }

    // The last DONE value is on top of the stack. If not DONE, call
    // IteratorClose.
                                                                  // ... OBJ ITER DONE
    InternalIfEmitter ifDone(this);
    if (!ifDone.emitThenElse())                                   // ... OBJ ITER
        return false;
    if (!emit1(JSOP_POP))                                         // ... OBJ
        return false;
    if (!ifDone.emitElse())                                       // ... OBJ ITER
        return false;
    if (!emitIteratorCloseInInnermostScope())                     // ... OBJ
        return false;
    if (!ifDone.emitEnd())
        return false;

    return true;
}

bool
BytecodeEmitter::emitComputedPropertyName(ParseNode* computedPropName)
{
    MOZ_ASSERT(computedPropName->isKind(ParseNodeKind::ComputedName));
    return emitTree(computedPropName->pn_kid) && emit1(JSOP_TOID);
}

bool
BytecodeEmitter::emitDestructuringOpsObject(ParseNode* pattern, DestructuringFlavor flav)
{
    MOZ_ASSERT(pattern->isKind(ParseNodeKind::Object));
    MOZ_ASSERT(pattern->isArity(PN_LIST));

    MOZ_ASSERT(this->stackDepth > 0);                             // ... RHS

    if (!emit1(JSOP_CHECKOBJCOERCIBLE))                           // ... RHS
        return false;

    bool needsRestPropertyExcludedSet = pattern->pn_count > 1 &&
                                        pattern->last()->isKind(ParseNodeKind::Spread);
    if (needsRestPropertyExcludedSet) {
        if (!emitDestructuringObjRestExclusionSet(pattern))       // ... RHS SET
            return false;

        if (!emit1(JSOP_SWAP))                                    // ... SET RHS
            return false;
    }

    for (ParseNode* member = pattern->pn_head; member; member = member->pn_next) {
        ParseNode* subpattern;
        if (member->isKind(ParseNodeKind::MutateProto) ||
            member->isKind(ParseNodeKind::Spread))
        {
            subpattern = member->pn_kid;
        } else {
            subpattern = member->pn_right;
        }

        ParseNode* lhs = subpattern;
        MOZ_ASSERT_IF(member->isKind(ParseNodeKind::Spread),
                      !lhs->isKind(ParseNodeKind::Assign));
        if (lhs->isKind(ParseNodeKind::Assign))
            lhs = lhs->pn_left;

        size_t emitted;
        if (!emitDestructuringLHSRef(lhs, &emitted))              // ... *SET RHS *LREF
            return false;

        // Duplicate the value being destructured to use as a reference base.
        if (!emitDupAt(emitted))                                  // ... *SET RHS *LREF RHS
            return false;

        if (member->isKind(ParseNodeKind::Spread)) {
            if (!updateSourceCoordNotes(member->pn_pos.begin))
                return false;

            if (!emitNewInit(JSProto_Object))                     // ... *SET RHS *LREF RHS TARGET
                return false;
            if (!emit1(JSOP_DUP))                                 // ... *SET RHS *LREF RHS TARGET TARGET
                return false;
            if (!emit2(JSOP_PICK, 2))                             // ... *SET RHS *LREF TARGET TARGET RHS
                return false;

            if (needsRestPropertyExcludedSet) {
                if (!emit2(JSOP_PICK, emitted + 4))               // ... RHS *LREF TARGET TARGET RHS SET
                    return false;
            }

            CopyOption option = needsRestPropertyExcludedSet
                                ? CopyOption::Filtered
                                : CopyOption::Unfiltered;
            if (!emitCopyDataProperties(option))                  // ... RHS *LREF TARGET
                return false;

            // Destructure TARGET per this member's lhs.
            if (!emitSetOrInitializeDestructuring(lhs, flav))     // ... RHS
                return false;

            MOZ_ASSERT(member == pattern->last(), "Rest property is always last");
            break;
        }

        // Now push the property name currently being matched, which is the
        // current property name "label" on the left of a colon in the object
        // initialiser.
        bool needsGetElem = true;

        if (member->isKind(ParseNodeKind::MutateProto)) {
            if (!emitAtomOp(cx->names().proto, JSOP_GETPROP))     // ... *SET RHS *LREF PROP
                return false;
            needsGetElem = false;
        } else {
            MOZ_ASSERT(member->isKind(ParseNodeKind::Colon) ||
                       member->isKind(ParseNodeKind::Shorthand));

            ParseNode* key = member->pn_left;
            if (key->isKind(ParseNodeKind::Number)) {
                if (!emitNumberOp(key->pn_dval))                  // ... *SET RHS *LREF RHS KEY
                    return false;
            } else if (key->isKind(ParseNodeKind::ObjectPropertyName) ||
                       key->isKind(ParseNodeKind::String))
            {
                if (!emitAtomOp(key->pn_atom, JSOP_GETPROP))      // ... *SET RHS *LREF PROP
                    return false;
                needsGetElem = false;
            } else {
                if (!emitComputedPropertyName(key))               // ... *SET RHS *LREF RHS KEY
                    return false;

                // Add the computed property key to the exclusion set.
                if (needsRestPropertyExcludedSet) {
                    if (!emitDupAt(emitted + 3))                  // ... SET RHS *LREF RHS KEY SET
                        return false;
                    if (!emitDupAt(1))                            // ... SET RHS *LREF RHS KEY SET KEY
                        return false;
                    if (!emit1(JSOP_UNDEFINED))                   // ... SET RHS *LREF RHS KEY SET KEY UNDEFINED
                        return false;
                    if (!emit1(JSOP_INITELEM))                    // ... SET RHS *LREF RHS KEY SET
                        return false;
                    if (!emit1(JSOP_POP))                         // ... SET RHS *LREF RHS KEY
                        return false;
                }
            }
        }

        // Get the property value if not done already.
        if (needsGetElem && !emitElemOpBase(JSOP_GETELEM))        // ... *SET RHS *LREF PROP
            return false;

        if (subpattern->isKind(ParseNodeKind::Assign)) {
            if (!emitDefault(subpattern->pn_right, lhs))          // ... *SET RHS *LREF VALUE
                return false;
        }

        // Destructure PROP per this member's lhs.
        if (!emitSetOrInitializeDestructuring(subpattern, flav))  // ... *SET RHS
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitDestructuringObjRestExclusionSet(ParseNode* pattern)
{
    MOZ_ASSERT(pattern->isKind(ParseNodeKind::Object));
    MOZ_ASSERT(pattern->isArity(PN_LIST));
    MOZ_ASSERT(pattern->last()->isKind(ParseNodeKind::Spread));

    ptrdiff_t offset = this->offset();
    if (!emitNewInit(JSProto_Object))
        return false;

    // Try to construct the shape of the object as we go, so we can emit a
    // JSOP_NEWOBJECT with the final shape instead.
    // In the case of computed property names and indices, we cannot fix the
    // shape at bytecode compile time. When the shape cannot be determined,
    // |obj| is nulled out.

    // No need to do any guessing for the object kind, since we know the upper
    // bound of how many properties we plan to have.
    gc::AllocKind kind = gc::GetGCObjectKind(pattern->pn_count - 1);
    RootedPlainObject obj(cx, NewBuiltinClassInstance<PlainObject>(cx, kind, TenuredObject));
    if (!obj)
        return false;

    RootedAtom pnatom(cx);
    for (ParseNode* member = pattern->pn_head; member; member = member->pn_next) {
        if (member->isKind(ParseNodeKind::Spread))
            break;

        bool isIndex = false;
        if (member->isKind(ParseNodeKind::MutateProto)) {
            pnatom.set(cx->names().proto);
        } else {
            ParseNode* key = member->pn_left;
            if (key->isKind(ParseNodeKind::Number)) {
                if (!emitNumberOp(key->pn_dval))
                    return false;
                isIndex = true;
            } else if (key->isKind(ParseNodeKind::ObjectPropertyName) ||
                       key->isKind(ParseNodeKind::String))
            {
                pnatom.set(key->pn_atom);
            } else {
                // Otherwise this is a computed property name which needs to
                // be added dynamically.
                obj.set(nullptr);
                continue;
            }
        }

        // Initialize elements with |undefined|.
        if (!emit1(JSOP_UNDEFINED))
            return false;

        if (isIndex) {
            obj.set(nullptr);
            if (!emit1(JSOP_INITELEM))
                return false;
        } else {
            uint32_t index;
            if (!makeAtomIndex(pnatom, &index))
                return false;

            if (obj) {
                MOZ_ASSERT(!obj->inDictionaryMode());
                Rooted<jsid> id(cx, AtomToId(pnatom));
                if (!NativeDefineProperty(cx, obj, id, UndefinedHandleValue, nullptr, nullptr,
                                          JSPROP_ENUMERATE))
                {
                    return false;
                }
                if (obj->inDictionaryMode())
                    obj.set(nullptr);
            }

            if (!emitIndex32(JSOP_INITPROP, index))
                return false;
        }
    }

    if (obj) {
        // The object survived and has a predictable shape: update the
        // original bytecode.
        if (!replaceNewInitWithNewObject(obj, offset))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitDestructuringOps(ParseNode* pattern, DestructuringFlavor flav)
{
    if (pattern->isKind(ParseNodeKind::Array))
        return emitDestructuringOpsArray(pattern, flav);
    return emitDestructuringOpsObject(pattern, flav);
}

bool
BytecodeEmitter::emitTemplateString(ParseNode* pn)
{
    MOZ_ASSERT(pn->isArity(PN_LIST));

    bool pushedString = false;

    for (ParseNode* pn2 = pn->pn_head; pn2 != NULL; pn2 = pn2->pn_next) {
        bool isString = (pn2->getKind() == ParseNodeKind::String ||
                         pn2->getKind() == ParseNodeKind::TemplateString);

        // Skip empty strings. These are very common: a template string like
        // `${a}${b}` has three empty strings and without this optimization
        // we'd emit four JSOP_ADD operations instead of just one.
        if (isString && pn2->pn_atom->empty())
            continue;

        if (!isString) {
            // We update source notes before emitting the expression
            if (!updateSourceCoordNotes(pn2->pn_pos.begin))
                return false;
        }

        if (!emitTree(pn2))
            return false;

        if (!isString) {
            // We need to convert the expression to a string
            if (!emit1(JSOP_TOSTRING))
                return false;
        }

        if (pushedString) {
            // We've pushed two strings onto the stack. Add them together, leaving just one.
            if (!emit1(JSOP_ADD))
                return false;
        } else {
            pushedString = true;
        }
    }

    if (!pushedString) {
        // All strings were empty, this can happen for something like `${""}`.
        // Just push an empty string.
        if (!emitAtomOp(cx->names().empty, JSOP_STRING))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitDeclarationList(ParseNode* declList)
{
    MOZ_ASSERT(declList->isArity(PN_LIST));
    MOZ_ASSERT(declList->isOp(JSOP_NOP));

    ParseNode* next;
    for (ParseNode* decl = declList->pn_head; decl; decl = next) {
        if (!updateSourceCoordNotes(decl->pn_pos.begin))
            return false;
        next = decl->pn_next;

        if (decl->isKind(ParseNodeKind::Assign)) {
            MOZ_ASSERT(decl->isOp(JSOP_NOP));

            ParseNode* pattern = decl->pn_left;
            MOZ_ASSERT(pattern->isKind(ParseNodeKind::Array) ||
                       pattern->isKind(ParseNodeKind::Object));

            if (!emitTree(decl->pn_right))
                return false;

            if (!emitDestructuringOps(pattern, DestructuringDeclaration))
                return false;

            if (!emit1(JSOP_POP))
                return false;
        } else {
            if (!emitSingleDeclaration(declList, decl, decl->expr()))
                return false;
        }
    }
    return true;
}

bool
BytecodeEmitter::emitSingleDeclaration(ParseNode* declList, ParseNode* decl,
                                       ParseNode* initializer)
{
    MOZ_ASSERT(decl->isKind(ParseNodeKind::Name));

    // Nothing to do for initializer-less 'var' declarations, as there's no TDZ.
    if (!initializer && declList->isKind(ParseNodeKind::Var)) {
        return true;
    }

    NameOpEmitter noe(this, decl->name(), NameOpEmitter::Kind::Initialize);
    if (!noe.prepareForRhs()) {                           // ENV?
        return false;
    }
    if (!initializer) {
        // Lexical declarations are initialized to undefined without an
        // initializer.
        MOZ_ASSERT(declList->isKind(ParseNodeKind::Let),
                   "var declarations without initializers handled above, "
                   "and const declarations must have initializers");
        if (!emit1(JSOP_UNDEFINED)) {                     // ENV? UNDEF
            return false;
        }
    } else {
        MOZ_ASSERT(initializer);
        if (!emitInitializer(initializer, decl)) {        // ENV? V
            return false;
        }
    }
    if (!noe.emitAssignment()) {                          // V
         return false;
    }
    if (!emit1(JSOP_POP)) {                               //
        return false;
    }

    return true;
}

bool BytecodeEmitter::emitAssignmentRhs(ParseNode* rhs,
                                        HandleAtom anonFunctionName) {
  if (rhs->isDirectRHSAnonFunction()) {
    if (anonFunctionName) {
      return emitAnonymousFunctionWithName(rhs, anonFunctionName);
    }
    return emitAnonymousFunctionWithComputedName(rhs, FunctionPrefixKind::None);
  }
  return emitTree(rhs);
}

// The RHS value to assign is already on the stack, i.e., the next enumeration
// value in a for-in or for-of loop. Offset is the location in the stack of the
// already-emitted rhs. If we emitted a BIND[G]NAME, then the scope is on the
// top of the stack and we need to dig one deeper to get the right RHS value.
bool BytecodeEmitter::emitAssignmentRhs(uint8_t offset) {
  if (offset != 1) {
    return emitPickN(offset - 1);
  }

  return true;
}

static inline JSOp
CompoundAssignmentParseNodeKindToJSOp(ParseNodeKind pnk)
{
    switch (pnk) {
      case ParseNodeKind::Assign:       return JSOP_NOP;
      case ParseNodeKind::AddAssign:    return JSOP_ADD;
      case ParseNodeKind::SubAssign:    return JSOP_SUB;
      case ParseNodeKind::BitOrAssign:  return JSOP_BITOR;
      case ParseNodeKind::BitXorAssign: return JSOP_BITXOR;
      case ParseNodeKind::BitAndAssign: return JSOP_BITAND;
      case ParseNodeKind::LshAssign:    return JSOP_LSH;
      case ParseNodeKind::RshAssign:    return JSOP_RSH;
      case ParseNodeKind::UrshAssign:   return JSOP_URSH;
      case ParseNodeKind::MulAssign:    return JSOP_MUL;
      case ParseNodeKind::DivAssign:    return JSOP_DIV;
      case ParseNodeKind::ModAssign:    return JSOP_MOD;
      case ParseNodeKind::PowAssign:    return JSOP_POW;
      case ParseNodeKind::CoalesceAssignExpr:
      case ParseNodeKind::OrAssignExpr:
      case ParseNodeKind::AndAssignExpr:
        // Short-circuit assignment operators are handled elsewhere.
        [[fallthrough]];
      default: MOZ_CRASH("unexpected compound assignment op");
    }
}

bool
BytecodeEmitter::emitAssignment(ParseNode* lhs, JSOp compoundOp, ParseNode* rhs)
{
    bool isCompound = compoundOp != JSOP_NOP;

    // Name assignments are handled separately because choosing ops and when
    // to emit BINDNAME is involved and should avoid duplication.
    if (lhs->isKind(ParseNodeKind::Name)) {
        RootedAtom name(cx, lhs->name());
        NameOpEmitter noe(this, name,
                          isCompound
                          ? NameOpEmitter::Kind::CompoundAssignment
                          : NameOpEmitter::Kind::SimpleAssignment);
        if (!noe.prepareForRhs()) {                       // ENV? VAL?
            return false;
        }

        if (rhs) {
            if (!emitAssignmentRhs(rhs, name)) {
                // ENV? VAL? RHS
                return false;
            }
        } else {
            uint8_t offset = noe.emittedBindOp() ? 2 : 1;
            // Assumption: Things with pre-emitted RHS values never need to be named.
            if (!emitAssignmentRhs(offset)) {
                //          [stack] ENV? VAL? RHS
                return false;
            }
        }

        // Emit the compound assignment op if there is one.
        if (isCompound) {
            if (!emit1(compoundOp)) {                     // ENV? VAL
                return false;
            }
        }
        if (!noe.emitAssignment()) {                      // VAL
            return false;
        }

        return true;
    }

    Maybe<PropOpEmitter> poe;
    Maybe<ElemOpEmitter> eoe;

    // Deal with non-name assignments.
    uint8_t offset = 1;

    RootedAtom anonFunctionName(cx);
    switch (lhs->getKind()) {
      case ParseNodeKind::Dot: {
        PropertyAccess* prop = &lhs->as<PropertyAccess>();
        bool isSuper = prop->isSuper();
        poe.emplace(this,
                    isCompound
                    ? PropOpEmitter::Kind::CompoundAssignment
                    : PropOpEmitter::Kind::SimpleAssignment,
                    isSuper
                    ? PropOpEmitter::ObjKind::Super
                    : PropOpEmitter::ObjKind::Other);
        if (!poe->prepareForObj()) {
            return false;
        }
        anonFunctionName = &prop->name();
        if (isSuper) {
            UnaryNode* base = &prop->expression().as<UnaryNode>();
            if (!emitGetThisForSuperBase(base)) {         // THIS SUPERBASE
                return false;
            }
            // SUPERBASE is pushed onto THIS later in poe->emitGet below.
            offset += 2;
        } else {
            if (!emitTree(&prop->expression())) {                // OBJ
                return false;
            }
            offset += 1;
        }
        break;
      }
      case ParseNodeKind::Elem: {
        PropertyByValue* elem = &lhs->as<PropertyByValue>();
        bool isSuper = elem->isSuper();
        eoe.emplace(this,
                    isCompound
                    ? ElemOpEmitter::Kind::CompoundAssignment
                    : ElemOpEmitter::Kind::SimpleAssignment,
                    isSuper
                    ? ElemOpEmitter::ObjKind::Super
                    : ElemOpEmitter::ObjKind::Other);
        if (!emitElemObjAndKey(elem, isSuper, *eoe)) {    // [Super]
            //                                            // THIS KEY
            //                                            // [Other]
            //                                            // OBJ KEY
            return false;
        }
        if (isSuper) {
            // SUPERBASE is pushed onto KEY in eoe->emitGet below.
            offset += 3;
        } else {
            offset += 2;
        }
        break;
      }
      case ParseNodeKind::Array:
      case ParseNodeKind::Object:
        break;
      case ParseNodeKind::Call:
        if (!emitTree(lhs))
            return false;

        // Assignment to function calls is forbidden, but we have to make the
        // call first.  Now we can throw.
        if (!emitUint16Operand(JSOP_THROWMSG, JSMSG_BAD_LEFTSIDE_OF_ASS))
            return false;

        // Rebalance the stack to placate stack-depth assertions.
        if (!emit1(JSOP_POP))
            return false;
        break;
      default:
        MOZ_ASSERT(0);
    }

    if (isCompound) {
        MOZ_ASSERT(rhs);
        switch (lhs->getKind()) {
          case ParseNodeKind::Dot: {
            PropertyAccess* prop = &lhs->as<PropertyAccess>();
            if (!poe->emitGet(prop->key().pn_atom)) {     // [Super]
                //                                        // THIS SUPERBASE PROP
                //                                        // [Other]
                //                                        // OBJ PROP
                return false;
            }
            break;
          }
          case ParseNodeKind::Elem: {
            if (!eoe->emitGet()) {                        // KEY THIS OBJ ELEM
                return false;
            }
            break;
          }
          case ParseNodeKind::Call:
            // We just emitted a JSOP_THROWMSG and popped the call's return
            // value.  Push a random value to make sure the stack depth is
            // correct.
            if (!emit1(JSOP_NULL))
                return false;
            break;
          default:;
        }
    }

    switch (lhs->getKind()) {
      case ParseNodeKind::Dot:
        if (!poe->prepareForRhs()) {                      // [Simple,Super]
            //                                            // THIS SUPERBASE
            //                                            // [Simple,Other]
            //                                            // OBJ
            //                                            // [Compound,Super]
            //                                            // THIS SUPERBASE PROP
            //                                            // [Compound,Other]
            //                                            // OBJ PROP
            return false;
        }
        break;
      case ParseNodeKind::Elem:
        if (!eoe->prepareForRhs()) {                      // [Simple,Super]
            //                                            // THIS KEY SUPERBASE
            //                                            // [Simple,Other]
            //                                            // OBJ KEY
            //                                            // [Compound,Super]
            //                                            // THIS KEY SUPERBASE ELEM
            //                                            // [Compound,Other]
            //                                            // OBJ KEY ELEM
            return false;
        }
        break;
      default:
        break;
    }


    // Purpose of anonFunctionName:
    // In normal property assignments (`obj.x = function(){}`), the anonymous
    // function does not have a computed name, and rhs->isDirectRHSAnonFunction()
    // will be false (and anonFunctionName will not be used). However, in field
    // initializers (`class C { x = function(){} }`), field initialization is
    // implemented via a property or elem assignment (where we are now), and
    // rhs->isDirectRHSAnonFunction() is set - so we'll assign the name of the
    // function.
    if (rhs) {
        if (!emitAssignmentRhs(rhs, anonFunctionName)) {
            //            [stack] ... VAL? RHS
            return false;
        }
    } else {
        // Assumption: Things with pre-emitted RHS values never need to be named.
        if (!emitAssignmentRhs(offset)) {
            //            [stack] ... VAL? RHS
            return false;
        }
    }

    /* If += etc., emit the binary operator with a source note. */
    if (isCompound) {
        if (!newSrcNote(SRC_ASSIGNOP)) {
            return false;
        }
        if (!emit1(compoundOp)) {                         // ... VAL
            return false;
        }
    }

    /* Finally, emit the specialized assignment bytecode. */
    switch (lhs->getKind()) {
      case ParseNodeKind::Dot: {
        PropertyAccess* prop = &lhs->as<PropertyAccess>();
        if (!poe->emitAssignment(prop->key().pn_atom)) {  // VAL
            return false;
        }

        poe.reset();
        break;
      }
      case ParseNodeKind::Call:
        // We threw above, so nothing to do here.
        break;
      case ParseNodeKind::Elem: {
        if (!eoe->emitAssignment()) {                     // VAL
            return false;
        }

        eoe.reset();
        break;
      }
      case ParseNodeKind::Array:
      case ParseNodeKind::Object:
        if (!emitDestructuringOps(lhs, DestructuringAssignment))
            return false;
        break;
      default:
        MOZ_ASSERT(0);
    }
    return true;
}

bool
ParseNode::getConstantValue(JSContext* cx, AllowConstantObjects allowObjects,
                            MutableHandleValue vp, Value* compare, size_t ncompare,
                            NewObjectKind newKind)
{
    MOZ_ASSERT(newKind == TenuredObject || newKind == SingletonObject);

    switch (getKind()) {
      case ParseNodeKind::Number:
        vp.setNumber(pn_dval);
        return true;
      case ParseNodeKind::TemplateString:
      case ParseNodeKind::String:
        vp.setString(pn_atom);
        return true;
      case ParseNodeKind::True:
        vp.setBoolean(true);
        return true;
      case ParseNodeKind::False:
        vp.setBoolean(false);
        return true;
      case ParseNodeKind::Null:
        vp.setNull();
        return true;
      case ParseNodeKind::RawUndefined:
        vp.setUndefined();
        return true;
      case ParseNodeKind::CallSiteObj:
      case ParseNodeKind::Array: {
        unsigned count;
        ParseNode* pn;

        if (allowObjects == DontAllowObjects) {
            vp.setMagic(JS_GENERIC_MAGIC);
            return true;
        }

        ObjectGroup::NewArrayKind arrayKind = ObjectGroup::NewArrayKind::Normal;
        if (allowObjects == ForCopyOnWriteArray) {
            arrayKind = ObjectGroup::NewArrayKind::CopyOnWrite;
            allowObjects = DontAllowObjects;
        }

        if (getKind() == ParseNodeKind::CallSiteObj) {
            count = pn_count - 1;
            pn = pn_head->pn_next;
        } else {
            MOZ_ASSERT(!(pn_xflags & PNX_NONCONST));
            count = pn_count;
            pn = pn_head;
        }

        AutoValueVector values(cx);
        if (!values.appendN(MagicValue(JS_ELEMENTS_HOLE), count))
            return false;
        size_t idx;
        for (idx = 0; pn; idx++, pn = pn->pn_next) {
            if (!pn->getConstantValue(cx, allowObjects, values[idx], values.begin(), idx))
                return false;
            if (values[idx].isMagic(JS_GENERIC_MAGIC)) {
                vp.setMagic(JS_GENERIC_MAGIC);
                return true;
            }
        }
        MOZ_ASSERT(idx == count);

        ArrayObject* obj = ObjectGroup::newArrayObject(cx, values.begin(), values.length(),
                                                       newKind, arrayKind);
        if (!obj)
            return false;

        if (!CombineArrayElementTypes(cx, obj, compare, ncompare))
            return false;

        vp.setObject(*obj);
        return true;
      }
      case ParseNodeKind::Object: {
        MOZ_ASSERT(!(pn_xflags & PNX_NONCONST));

        if (allowObjects == DontAllowObjects) {
            vp.setMagic(JS_GENERIC_MAGIC);
            return true;
        }
        MOZ_ASSERT(allowObjects == AllowObjects);

        Rooted<IdValueVector> properties(cx, IdValueVector(cx));

        RootedValue value(cx), idvalue(cx);
        for (ParseNode* pn = pn_head; pn; pn = pn->pn_next) {
            if (!pn->pn_right->getConstantValue(cx, allowObjects, &value))
                return false;
            if (value.isMagic(JS_GENERIC_MAGIC)) {
                vp.setMagic(JS_GENERIC_MAGIC);
                return true;
            }

            ParseNode* pnid = pn->pn_left;
            if (pnid->isKind(ParseNodeKind::Number)) {
                idvalue = NumberValue(pnid->pn_dval);
            } else {
                MOZ_ASSERT(pnid->isKind(ParseNodeKind::ObjectPropertyName) ||
                           pnid->isKind(ParseNodeKind::String));
                MOZ_ASSERT(pnid->pn_atom != cx->names().proto);
                idvalue = StringValue(pnid->pn_atom);
            }

            RootedId id(cx);
            if (!ValueToId<CanGC>(cx, idvalue, &id))
                return false;

            if (!properties.append(IdValuePair(id, value)))
                return false;
        }

        JSObject* obj = ObjectGroup::newPlainObject(cx, properties.begin(), properties.length(),
                                                    newKind);
        if (!obj)
            return false;

        if (!CombinePlainObjectPropertyTypes(cx, obj, compare, ncompare))
            return false;

        vp.setObject(*obj);
        return true;
      }
      default:
        MOZ_CRASH("Unexpected node");
    }
    return false;
}

bool
BytecodeEmitter::emitSingletonInitialiser(ParseNode* pn)
{
    NewObjectKind newKind =
        (pn->getKind() == ParseNodeKind::Object) ? SingletonObject : TenuredObject;

    RootedValue value(cx);
    if (!pn->getConstantValue(cx, ParseNode::AllowObjects, &value, nullptr, 0, newKind))
        return false;

    MOZ_ASSERT_IF(newKind == SingletonObject, value.toObject().isSingleton());

    ObjectBox* objbox = parser.newObjectBox(&value.toObject());
    if (!objbox)
        return false;

    return emitObjectOp(objbox, JSOP_OBJECT);
}

bool BytecodeEmitter::emitShortCircuitAssignment(ParseNode* pn) {
  MOZ_ASSERT(pn->isArity(PN_BINARY));
  MOZ_ASSERT(pn->isKind(ParseNodeKind::CoalesceAssignExpr) ||
             pn->isKind(ParseNodeKind::OrAssignExpr) ||
             pn->isKind(ParseNodeKind::AndAssignExpr));

  TDZCheckCache tdzCache(this);

  JSOp op;
  switch (pn->getKind()) {
    case ParseNodeKind::CoalesceAssignExpr:
      op = JSOP_COALESCE;
      break;
    case ParseNodeKind::OrAssignExpr:
      op = JSOP_OR;
      break;
    case ParseNodeKind::AndAssignExpr:
      op = JSOP_AND;
      break;
    default:
      MOZ_CRASH("Unexpected ParseNodeKind");
  }

  ParseNode* lhs = pn->pn_left;
  ParseNode* rhs = pn->pn_right;

  // |name| is used within NameOpEmitter, so its lifetime must surpass |noe|.
  RootedAtom name(cx);

  // Select the appropriate emitter based on the left-hand side.
  Maybe<NameOpEmitter> noe;
  Maybe<PropOpEmitter> poe;
  Maybe<ElemOpEmitter> eoe;

  int32_t depth = stackDepth;

  // Number of values pushed onto the stack in addition to the lhs value.
  int32_t numPushed;

  // Evaluate the left-hand side expression and compute any stack values needed
  // for the assignment.
  switch (lhs->getKind()) {
    case ParseNodeKind::Name: {
      name = lhs->as<NameNode>().name();
      noe.emplace(this, name, NameOpEmitter::Kind::CompoundAssignment);

      if (!noe->prepareForRhs()) {
        //          [stack] ENV? LHS
        return false;
      }

      numPushed = noe->emittedBindOp();
      break;
    }

    case ParseNodeKind::Dot: {
      PropertyAccess* prop = &lhs->as<PropertyAccess>();
      bool isSuper = prop->isSuper();

      poe.emplace(this, PropOpEmitter::Kind::CompoundAssignment,
                  isSuper ? PropOpEmitter::ObjKind::Super
                          : PropOpEmitter::ObjKind::Other);

      if (!poe->prepareForObj()) {
        return false;
      }

      if (isSuper) {
        UnaryNode* base = &prop->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {
          //        [stack] THIS SUPERBASE
          return false;
        }
      } else {
        if (!emitTree(&prop->expression())) {
          //        [stack] OBJ
          return false;
        }
      }

      if (!poe->emitGet(prop->key().pn_atom)) {
        //          [stack] # if Super
        //          [stack] THIS SUPERBASE LHS
        //          [stack] # otherwise
        //          [stack] OBJ LHS
        return false;
      }

      if (!poe->prepareForRhs()) {
        //          [stack] # if Super
        //          [stack] THIS SUPERBASE LHS
        //          [stack] # otherwise
        //          [stack] OBJ LHS
        return false;
      }

      numPushed = 1 + isSuper;
      break;
    }

    case ParseNodeKind::Elem: {
      PropertyByValue* elem = &lhs->as<PropertyByValue>();
      bool isSuper = elem->isSuper();

      eoe.emplace(this, ElemOpEmitter::Kind::CompoundAssignment,
                  isSuper ? ElemOpEmitter::ObjKind::Super
                          : ElemOpEmitter::ObjKind::Other);

      if (!emitElemObjAndKey(elem, isSuper, *eoe)) {
        //          [stack] # if Super
        //          [stack] THIS KEY
        //          [stack] # otherwise
        //          [stack] OBJ KEY
        return false;
      }

      if (!eoe->emitGet()) {
        //          [stack] # if Super
        //          [stack] THIS KEY SUPERBASE LHS
        //          [stack] # otherwise
        //          [stack] OBJ KEY LHS
        return false;
      }

      if (!eoe->prepareForRhs()) {
        //          [stack] # if Super
        //          [stack] THIS KEY SUPERBASE LHS
        //          [stack] # otherwise
        //          [stack] OBJ KEY LHS
        return false;
      }

      numPushed = 2 + isSuper;
      break;
    }

    default:
      MOZ_CRASH();
  }

  MOZ_ASSERT(stackDepth == depth + numPushed + 1);

  // Test for the short-circuit condition.
  JumpList jump;
  if (!emitJump(op, &jump)) {
    //              [stack] ... LHS
    return false;
  }

  // The short-circuit condition wasn't fulfilled, pop the left-hand side value
  // which was kept on the stack.
  if (!emit1(JSOP_POP)) {
    //              [stack] ...
    return false;
  }

  if (!emitAssignmentRhs(rhs, name)) {
    //              [stack] ... RHS
    return false;
  }

  // Perform the actual assignment.
  switch (lhs->getKind()) {
    case ParseNodeKind::Name: {
      if (!noe->emitAssignment()) {
        //          [stack] RHS
        return false;
      }
      break;
    }

    case ParseNodeKind::Dot: {
      PropertyAccess* prop = &lhs->as<PropertyAccess>();

      if (!poe->emitAssignment(prop->key().pn_atom)) {
        //          [stack] RHS
        return false;
      }
      break;
    }

    case ParseNodeKind::Elem: {
      if (!eoe->emitAssignment()) {
        //          [stack] RHS
        return false;
      }
      break;
    }

    default:
      MOZ_CRASH();
  }

  MOZ_ASSERT(stackDepth == depth + 1);

  // Join with the short-circuit jump and pop anything left on the stack.
  if (numPushed > 0) {
    JumpList jumpAroundPop;
    if (!emitJump(JSOP_GOTO, &jumpAroundPop)) {
      //            [stack] RHS
      return false;
    }

    if (!emitJumpTargetAndPatch(jump)) {
      //            [stack] ... LHS
      return false;
    }

    // Reconstruct the stack depth after the jump.
    stackDepth = depth + 1 + numPushed;

    // Move the left-hand side value to the bottom and pop the rest.
    if (!emitUnpickN(numPushed)) {
      //            [stack] LHS ...
      return false;
    }
    if (!emitPopN(numPushed)) {
      //            [stack] LHS
      return false;
    }

    if (!emitJumpTargetAndPatch(jumpAroundPop)) {
      //            [stack] LHS | RHS
      return false;
    }
  } else {
    if (!emitJumpTargetAndPatch(jump)) {
      //            [stack] LHS | RHS
      return false;
    }
  }

  MOZ_ASSERT(stackDepth == depth + 1);

  return true;
}

bool
BytecodeEmitter::emitCallSiteObject(ParseNode* pn)
{
    RootedValue value(cx);
    if (!pn->getConstantValue(cx, ParseNode::AllowObjects, &value))
        return false;

    MOZ_ASSERT(value.isObject());

    ObjectBox* objbox1 = parser.newObjectBox(&value.toObject());
    if (!objbox1)
        return false;

    if (!pn->as<CallSiteNode>().getRawArrayValue(cx, &value))
        return false;

    MOZ_ASSERT(value.isObject());

    ObjectBox* objbox2 = parser.newObjectBox(&value.toObject());
    if (!objbox2)
        return false;

    return emitObjectPairOp(objbox1, objbox2, JSOP_CALLSITEOBJ);
}

/* See the SRC_FOR source note offsetBias comments later in this file. */
JS_STATIC_ASSERT(JSOP_NOP_LENGTH == 1);
JS_STATIC_ASSERT(JSOP_POP_LENGTH == 1);

namespace {

class EmitLevelManager
{
    BytecodeEmitter* bce;
  public:
    explicit EmitLevelManager(BytecodeEmitter* bce) : bce(bce) { bce->emitLevel++; }
    ~EmitLevelManager() { bce->emitLevel--; }
};

} /* anonymous namespace */

bool
BytecodeEmitter::emitCatch(ParseNode* pn)
{
    // We must be nested under a try-finally statement.
    TryFinallyControl& controlInfo = innermostNestableControl->as<TryFinallyControl>();

    /*
     * Dup the exception object if there is a guard for rethrowing to use
     * it later when rethrowing or in other catches.
     */
    if (pn->pn_kid2 && !emit1(JSOP_DUP))
        return false;

    ParseNode* pn2 = pn->pn_kid1;
    if (!pn2) {
        // Catch parameter was omitted; just discard the exception.
        if (!emit1(JSOP_POP))
            return false;
    } else {
        switch (pn2->getKind()) {
          case ParseNodeKind::Array:
          case ParseNodeKind::Object:
            if (!emitDestructuringOps(pn2, DestructuringDeclaration))
                return false;
            if (!emit1(JSOP_POP))
                return false;
            break;

          case ParseNodeKind::Name:
            if (!emitLexicalInitialization(pn2))
                return false;
            if (!emit1(JSOP_POP))
                return false;
            break;

          default:
            MOZ_ASSERT(0);
        }
    }

    // If there is a guard expression, emit it and arrange to jump to the next
    // catch block if the guard expression is false.
    if (pn->pn_kid2) {
        if (!emitTree(pn->pn_kid2))
            return false;

        // If the guard expression is false, fall through, pop the block scope,
        // and jump to the next catch block.  Otherwise jump over that code and
        // pop the dupped exception.
        JumpList guardCheck;
        if (!emitJump(JSOP_IFNE, &guardCheck))
            return false;

        {
            NonLocalExitControl nle(this, NonLocalExitControl::Throw);

            // Move exception back to cx->exception to prepare for
            // the next catch.
            if (!emit1(JSOP_THROWING))
                return false;

            // Leave the scope for this catch block.
            if (!nle.prepareForNonLocalJump(&controlInfo))
                return false;

            // Jump to the next handler added by emitTry.
            if (!emitJump(JSOP_GOTO, &controlInfo.guardJump))
                return false;
        }

        // Back to normal control flow.
        if (!emitJumpTargetAndPatch(guardCheck))
            return false;

        // Pop duplicated exception object as we no longer need it.
        if (!emit1(JSOP_POP))
            return false;
    }

    /* Emit the catch body. */
    return emitTree(pn->pn_kid3);
}

// Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047. See the
// comment on EmitSwitch.
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitTry(ParseNode* pn)
{
    ParseNode* catchList = pn->pn_kid2;
    ParseNode* finallyNode = pn->pn_kid3;

    TryEmitter::Kind kind;
    if (catchList) {
        if (finallyNode)
            kind = TryEmitter::Kind::TryCatchFinally;
        else
            kind = TryEmitter::Kind::TryCatch;
    } else {
        MOZ_ASSERT(finallyNode);
        kind = TryEmitter::Kind::TryFinally;
    }
    TryEmitter tryCatch(this, kind, TryEmitter::ControlKind::Syntactic);

    if (!tryCatch.emitTry())
        return false;

    if (!emitTree(pn->pn_kid1))
        return false;

    // If this try has a catch block, emit it.
    if (catchList) {
        MOZ_ASSERT(catchList->isKind(ParseNodeKind::CatchList));

        // The emitted code for a catch block looks like:
        //
        // [pushlexicalenv]             only if any local aliased
        // exception
        // if there is a catchguard:
        //   dup
        // setlocal 0; pop              assign or possibly destructure exception
        // if there is a catchguard:
        //   < catchguard code >
        //   ifne POST
        //   debugleaveblock
        //   [poplexicalenv]            only if any local aliased
        //   throwing                   pop exception to cx->exception
        //   goto <next catch block>
        //   POST: pop
        // < catch block contents >
        // debugleaveblock
        // [poplexicalenv]              only if any local aliased
        // goto <end of catch blocks>   non-local; finally applies
        //
        // If there's no catch block without a catchguard, the last <next catch
        // block> points to rethrow code.  This code will [gosub] to the finally
        // code if appropriate, and is also used for the catch-all trynote for
        // capturing exceptions thrown from catch{} blocks.
        //
        for (ParseNode* pn3 = catchList->pn_head; pn3; pn3 = pn3->pn_next) {
            if (!tryCatch.emitCatch())
                return false;

            // Emit the lexical scope and catch body.
            MOZ_ASSERT(pn3->isKind(ParseNodeKind::LexicalScope));
            if (!emitTree(pn3))
                return false;
        }
    }

    // Emit the finally handler, if there is one.
    if (finallyNode) {
        if (!tryCatch.emitFinally(Some(finallyNode->pn_pos.begin)))
            return false;

        if (!emitTree(finallyNode))
            return false;
    }

    if (!tryCatch.emitEnd())
        return false;

    return true;
}

bool
BytecodeEmitter::emitIf(ParseNode* pn)
{
    IfEmitter ifThenElse(this);

  if_again:
    /* Emit code for the condition before pushing stmtInfo. */
    if (!emitTree(pn->pn_kid1))
        return false;

    ParseNode* elseNode = pn->pn_kid3;
    if (elseNode) {
        if (!ifThenElse.emitThenElse())
            return false;
    } else {
        if (!ifThenElse.emitThen())
            return false;
    }

    /* Emit code for the then part. */
    if (!emitTree(pn->pn_kid2))
        return false;

    if (elseNode) {
        if (elseNode->isKind(ParseNodeKind::If)) {
            pn = elseNode;

            if (!ifThenElse.emitElseIf())
                return false;

            goto if_again;
        }

        if (!ifThenElse.emitElse())
            return false;

        /* Emit code for the else part. */
        if (!emitTree(elseNode))
            return false;
    }

    if (!ifThenElse.emitEnd())
        return false;

    return true;
}

bool
BytecodeEmitter::emitHoistedFunctionsInList(ParseNode* list)
{
    MOZ_ASSERT(list->pn_xflags & PNX_FUNCDEFS);

    for (ParseNode* pn = list->pn_head; pn; pn = pn->pn_next) {
        ParseNode* maybeFun = pn;

        if (!sc->strict()) {
            while (maybeFun->isKind(ParseNodeKind::Label))
                maybeFun = maybeFun->as<LabeledStatement>().statement();
        }

        if (maybeFun->isKind(ParseNodeKind::Function) && maybeFun->functionIsHoisted()) {
            if (!emitTree(maybeFun))
                return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitLexicalScopeBody(ParseNode* body, EmitLineNumberNote emitLineNote)
{
    if (body->isKind(ParseNodeKind::StatementList) && body->pn_xflags & PNX_FUNCDEFS) {
        // This block contains function statements whose definitions are
        // hoisted to the top of the block. Emit these as a separate pass
        // before the rest of the block.
        if (!emitHoistedFunctionsInList(body))
            return false;
    }

    // Line notes were updated by emitLexicalScope.
    return emitTree(body, ValueUsage::WantValue, emitLineNote);
}

// Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047. See
// the comment on emitSwitch.
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitLexicalScope(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::LexicalScope));

    TDZCheckCache tdzCache(this);

    ParseNode* body = pn->scopeBody();
    if (pn->isEmptyScope())
        return emitLexicalScopeBody(body);

    // Update line number notes before emitting TDZ poison in
    // EmitterScope::enterLexical to avoid spurious pausing on seemingly
    // non-effectful lines in Debugger.
    //
    // For example, consider the following code.
    //
    // L1: {
    // L2:   let x = 42;
    // L3: }
    //
    // If line number notes were not updated before the TDZ poison, the TDZ
    // poison bytecode sequence of 'uninitialized; initlexical' will have line
    // number L1, and the Debugger will pause there.
    if (!ParseNodeRequiresSpecialLineNumberNotes(body)) {
        ParseNode* pnForPos = body;
        if (body->isKind(ParseNodeKind::StatementList) && body->pn_head)
            pnForPos = body->pn_head;
        if (!updateLineNumberNotes(pnForPos->pn_pos.begin))
            return false;
    }

    EmitterScope emitterScope(this);
    ScopeKind kind;
    if (body->isKind(ParseNodeKind::Catch))
        kind = (!body->pn_kid1 || body->pn_kid1->isKind(ParseNodeKind::Name))
               ? ScopeKind::SimpleCatch
               : ScopeKind::Catch;
    else
        kind = ScopeKind::Lexical;

    if (!emitterScope.enterLexical(this, kind, pn->scopeBindings()))
        return false;

    if (body->isKind(ParseNodeKind::For)) {
        // for loops need to emit {FRESHEN,RECREATE}LEXICALENV if there are
        // lexical declarations in the head. Signal this by passing a
        // non-nullptr lexical scope.
        if (!emitFor(body, &emitterScope))
            return false;
    } else {
        if (!emitLexicalScopeBody(body, SUPPRESS_LINENOTE))
            return false;
    }

    return emitterScope.leave(this);
}

bool
BytecodeEmitter::emitWith(ParseNode* pn)
{
    if (!emitTree(pn->pn_left))
        return false;

    EmitterScope emitterScope(this);
    if (!emitterScope.enterWith(this))
        return false;

    if (!emitTree(pn->pn_right))
        return false;

    return emitterScope.leave(this);
}

bool
BytecodeEmitter::emitCopyDataProperties(CopyOption option)
{
    DebugOnly<int32_t> depth = this->stackDepth;

    uint32_t argc;
    if (option == CopyOption::Filtered) {
        MOZ_ASSERT(depth > 2);                 // TARGET SOURCE SET
        argc = 3;

        if (!emitAtomOp(cx->names().CopyDataProperties,
                        JSOP_GETINTRINSIC))    // TARGET SOURCE SET COPYDATAPROPERTIES
        {
            return false;
        }
    } else {
        MOZ_ASSERT(depth > 1);                 // TARGET SOURCE
        argc = 2;

        if (!emitAtomOp(cx->names().CopyDataPropertiesUnfiltered,
                        JSOP_GETINTRINSIC))    // TARGET SOURCE COPYDATAPROPERTIES
        {
            return false;
        }
    }

    if (!emit1(JSOP_UNDEFINED))                // TARGET SOURCE *SET COPYDATAPROPERTIES UNDEFINED
        return false;
    if (!emit2(JSOP_PICK, argc + 1))           // SOURCE *SET COPYDATAPROPERTIES UNDEFINED TARGET
        return false;
    if (!emit2(JSOP_PICK, argc + 1))           // *SET COPYDATAPROPERTIES UNDEFINED TARGET SOURCE
        return false;
    if (option == CopyOption::Filtered) {
        if (!emit2(JSOP_PICK, argc + 1))       // COPYDATAPROPERTIES UNDEFINED TARGET SOURCE SET
            return false;
    }
    if (!emitCall(JSOP_CALL_IGNORES_RV, argc)) // IGNORED
        return false;
    checkTypeSet(JSOP_CALL_IGNORES_RV);

    if (!emit1(JSOP_POP))                      // -
        return false;

    MOZ_ASSERT(depth - int(argc) == this->stackDepth);
    return true;
}

bool
BytecodeEmitter::emitIterator()
{
    // Convert iterable to iterator.
    if (!emit1(JSOP_DUP))                                         // OBJ OBJ
        return false;
    if (!emit2(JSOP_SYMBOL, uint8_t(JS::SymbolCode::iterator)))   // OBJ OBJ @@ITERATOR
        return false;
    if (!emitElemOpBase(JSOP_CALLELEM))                           // OBJ ITERFN
        return false;
    if (!emit1(JSOP_SWAP))                                        // ITERFN OBJ
        return false;
    if (!emitCall(JSOP_CALLITER, 0))                              // ITER
        return false;
    checkTypeSet(JSOP_CALLITER);
    if (!emitCheckIsObj(CheckIsObjectKind::GetIterator))          // ITER
        return false;
    return true;
}

bool
BytecodeEmitter::emitAsyncIterator()
{
    // Convert iterable to iterator.
    if (!emit1(JSOP_DUP))                                         // OBJ OBJ
        return false;
    if (!emit2(JSOP_SYMBOL, uint8_t(JS::SymbolCode::asyncIterator))) // OBJ OBJ @@ASYNCITERATOR
        return false;
    if (!emitElemOpBase(JSOP_CALLELEM))                           // OBJ ITERFN
        return false;

    InternalIfEmitter ifAsyncIterIsUndefined(this);
    if (!emitPushNotUndefinedOrNull())                            // OBJ ITERFN !UNDEF-OR-NULL
        return false;
    if (!emit1(JSOP_NOT))                                         // OBJ ITERFN UNDEF-OR-NULL
        return false;
    if (!ifAsyncIterIsUndefined.emitThenElse())                   // OBJ ITERFN
        return false;

    if (!emit1(JSOP_POP))                                         // OBJ
        return false;
    if (!emit1(JSOP_DUP))                                         // OBJ OBJ
        return false;
    if (!emit2(JSOP_SYMBOL, uint8_t(JS::SymbolCode::iterator)))   // OBJ OBJ @@ITERATOR
        return false;
    if (!emitElemOpBase(JSOP_CALLELEM))                           // OBJ ITERFN
        return false;
    if (!emit1(JSOP_SWAP))                                        // ITERFN OBJ
        return false;
    if (!emitCall(JSOP_CALLITER, 0))                              // ITER
        return false;
    checkTypeSet(JSOP_CALLITER);
    if (!emitCheckIsObj(CheckIsObjectKind::GetIterator))          // ITER
        return false;

    if (!emit1(JSOP_TOASYNCITER))                                 // ITER
        return false;

    if (!ifAsyncIterIsUndefined.emitElse())                       // OBJ ITERFN
        return false;

    if (!emit1(JSOP_SWAP))                                        // ITERFN OBJ
        return false;
    if (!emitCall(JSOP_CALLITER, 0))                              // ITER
        return false;
    checkTypeSet(JSOP_CALLITER);
    if (!emitCheckIsObj(CheckIsObjectKind::GetIterator))          // ITER
        return false;

    if (!ifAsyncIterIsUndefined.emitEnd())                        // ITER
        return false;

    return true;
}

bool
BytecodeEmitter::emitSpread(bool allowSelfHosted)
{
    LoopControl loopInfo(this, StatementKind::Spread);

    // Jump down to the loop condition to minimize overhead assuming at least
    // one iteration, as the other loop forms do.  Annotate so IonMonkey can
    // find the loop-closing jump.
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR_OF, &noteIndex))
        return false;

    // Jump down to the loop condition to minimize overhead, assuming at least
    // one iteration.  (This is also what we do for loops; whether this
    // assumption holds for spreads is an unanswered question.)
    JumpList initialJump;
    if (!emitJump(JSOP_GOTO, &initialJump))               // ITER ARR I (during the goto)
        return false;

    JumpTarget top{ -1 };
    if (!emitLoopHead(nullptr, &top))                     // ITER ARR I
        return false;

    // When we enter the goto above, we have ITER ARR I on the stack.  But when
    // we reach this point on the loop backedge (if spreading produces at least
    // one value), we've additionally pushed a RESULT iteration value.
    // Increment manually to reflect this.
    this->stackDepth++;

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    {
#ifdef DEBUG
        auto loopDepth = this->stackDepth;
#endif

        // Emit code to assign result.value to the iteration variable.
        if (!emitAtomOp(cx->names().value, JSOP_GETPROP)) // ITER ARR I VALUE
            return false;
        if (!emit1(JSOP_INITELEM_INC))                    // ITER ARR (I+1)
            return false;

        MOZ_ASSERT(this->stackDepth == loopDepth - 1);

        // Spread operations can't contain |continue|, so don't bother setting loop
        // and enclosing "update" offsets, as we do with for-loops.

        // COME FROM the beginning of the loop to here.
        if (!emitLoopEntry(nullptr, initialJump))         // ITER ARR I
            return false;

        if (!emitDupAt(2))                                // ITER ARR I ITER
            return false;
        if (!emitIteratorNext(nullptr, IteratorKind::Sync, allowSelfHosted))  // ITER ARR I RESULT
            return false;
        if (!emit1(JSOP_DUP))                             // ITER ARR I RESULT RESULT
            return false;
        if (!emitAtomOp(cx->names().done, JSOP_GETPROP))  // ITER ARR I RESULT DONE
            return false;

        if (!emitBackwardJump(JSOP_IFEQ, top, &beq, &breakTarget)) // ITER ARR I RESULT
            return false;

        MOZ_ASSERT(this->stackDepth == loopDepth);
    }

    // Let Ion know where the closing jump of this loop is.
    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - initialJump.offset))
        return false;

    // No breaks or continues should occur in spreads.
    MOZ_ASSERT(loopInfo.breaks.offset == -1);
    MOZ_ASSERT(loopInfo.continues.offset == -1);

    if (!tryNoteList.append(JSTRY_FOR_OF, stackDepth, top.offset, breakTarget.offset))
        return false;

    if (!emit2(JSOP_PICK, 3))                             // ARR FINAL_INDEX RESULT ITER
        return false;

    return emitPopN(2);                                   // ARR FINAL_INDEX
}

bool
BytecodeEmitter::emitInitializeForInOrOfTarget(ParseNode* forHead)
{
    MOZ_ASSERT(forHead->isKind(ParseNodeKind::ForIn) ||
               forHead->isKind(ParseNodeKind::ForOf));
    MOZ_ASSERT(forHead->isArity(PN_TERNARY));

    MOZ_ASSERT(this->stackDepth >= 1,
               "must have a per-iteration value for initializing");

    ParseNode* target = forHead->pn_kid1;
    MOZ_ASSERT(!forHead->pn_kid2);

    // If the for-in/of loop didn't have a variable declaration, per-loop
    // initialization is just assigning the iteration value to a target
    // expression.
    if (!parser.isDeclarationList(target))
        return emitAssignment(target, JSOP_NOP, nullptr); // ... ITERVAL

    // Otherwise, per-loop initialization is (possibly) declaration
    // initialization.  If the declaration is a lexical declaration, it must be
    // initialized.  If the declaration is a variable declaration, an
    // assignment to that name (which does *not* necessarily assign to the
    // variable!) must be generated.

    if (!updateSourceCoordNotes(target->pn_pos.begin))
        return false;

    MOZ_ASSERT(target->isForLoopDeclaration());
    target = parser.singleBindingFromDeclaration(target);

    if (target->isKind(ParseNodeKind::Name)) {
        NameOpEmitter noe(this, target->name(), NameOpEmitter::Kind::Initialize);
        if (!noe.prepareForRhs()) {
            return false;
        }
        if (noe.emittedBindOp()) {
            // Per-iteration initialization in for-in/of loops computes the
            // iteration value *before* initializing.  Thus the initializing
            // value may be buried under a bind-specific value on the stack.
            // Swap it to the top of the stack.
            MOZ_ASSERT(stackDepth >= 2);
            if (!emit1(JSOP_SWAP)) {
                return false;
            }
        } else {
             // In cases of emitting a frame slot or environment slot,
             // nothing needs be done.
            MOZ_ASSERT(stackDepth >= 1);
        }
        if (!noe.emitAssignment()) {
            return false;
        }

        // The caller handles removing the iteration value from the stack.
        return true;
    }

    MOZ_ASSERT(!target->isKind(ParseNodeKind::Assign),
               "for-in/of loop destructuring declarations can't have initializers");

    MOZ_ASSERT(target->isKind(ParseNodeKind::Array) ||
               target->isKind(ParseNodeKind::Object));
    return emitDestructuringOps(target, DestructuringDeclaration);
}

bool
BytecodeEmitter::emitForOf(ParseNode* forOfLoop, EmitterScope* headLexicalEmitterScope)
{
    MOZ_ASSERT(forOfLoop->isKind(ParseNodeKind::For));
    MOZ_ASSERT(forOfLoop->isArity(PN_BINARY));

    ParseNode* forOfHead = forOfLoop->pn_left;
    MOZ_ASSERT(forOfHead->isKind(ParseNodeKind::ForOf));
    MOZ_ASSERT(forOfHead->isArity(PN_TERNARY));

    unsigned iflags = forOfLoop->pn_iflags;
    IteratorKind iterKind = (iflags & JSITER_FORAWAITOF)
                            ? IteratorKind::Async
                            : IteratorKind::Sync;
    MOZ_ASSERT_IF(iterKind == IteratorKind::Async, sc->asFunctionBox());
    MOZ_ASSERT_IF(iterKind == IteratorKind::Async, sc->asFunctionBox()->isAsync());

    ParseNode* forHeadExpr = forOfHead->pn_kid3;

    // Certain builtins (e.g. Array.from) are implemented in self-hosting
    // as for-of loops.
    bool allowSelfHostedIter = false;
    if (emitterMode == BytecodeEmitter::SelfHosting &&
        forHeadExpr->isKind(ParseNodeKind::Call) &&
        forHeadExpr->pn_left->name() == cx->names().allowContentIter)
    {
        allowSelfHostedIter = true;
    }

    // Evaluate the expression being iterated. The forHeadExpr should use a
    // distinct TDZCheckCache to evaluate since (abstractly) it runs in its own
    // LexicalEnvironment.
    if (!emitTreeInBranch(forHeadExpr))                   // ITERABLE
        return false;
    if (iterKind == IteratorKind::Async) {
        if (!emitAsyncIterator())                         // ITER
            return false;
    } else {
        if (!emitIterator())                              // ITER
            return false;
    }

    int32_t iterDepth = stackDepth;

    // For-of loops have both the iterator and the result.value on the stack.
    // Push an undefined to balance the stack.
    if (!emit1(JSOP_UNDEFINED))                           // ITER UNDEF
        return false;

    ForOfLoopControl loopInfo(this, iterDepth, allowSelfHostedIter, iterKind);

    // Annotate so IonMonkey can find the loop-closing jump.
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR_OF, &noteIndex))
        return false;

    JumpList initialJump;
    if (!emitJump(JSOP_GOTO, &initialJump))               // ITER UNDEF
        return false;

    JumpTarget top{ -1 };
    if (!emitLoopHead(nullptr, &top))                     // ITER UNDEF
        return false;

    // If the loop had an escaping lexical declaration, replace the current
    // environment with an dead zoned one to implement TDZ semantics.
    if (headLexicalEmitterScope) {
        // The environment chain only includes an environment for the for-of
        // loop head *if* a scope binding is captured, thereby requiring
        // recreation each iteration. If a lexical scope exists for the head,
        // it must be the innermost one. If that scope has closed-over
        // bindings inducing an environment, recreate the current environment.
        DebugOnly<ParseNode*> forOfTarget = forOfHead->pn_kid1;
        MOZ_ASSERT(forOfTarget->isKind(ParseNodeKind::Let) ||
                   forOfTarget->isKind(ParseNodeKind::Const));
        MOZ_ASSERT(headLexicalEmitterScope == innermostEmitterScope());
        MOZ_ASSERT(headLexicalEmitterScope->scope(this)->kind() == ScopeKind::Lexical);

        if (headLexicalEmitterScope->hasEnvironment()) {
            if (!emit1(JSOP_RECREATELEXICALENV))          // ITER UNDEF
                return false;
        }

        // For uncaptured bindings, put them back in TDZ.
        if (!headLexicalEmitterScope->deadZoneFrameSlots(this))
            return false;
    }

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    {
#ifdef DEBUG
        auto loopDepth = this->stackDepth;
#endif

        // Make sure this code is attributed to the "for".
        if (!updateSourceCoordNotes(forOfHead->pn_pos.begin))
            return false;

        if (!emit1(JSOP_POP))                             // ITER
            return false;
        if (!emit1(JSOP_DUP))                             // ITER ITER
            return false;

        if (!emitIteratorNext(forOfHead, iterKind, allowSelfHostedIter))
            return false;                                 // ITER RESULT

        if (!emit1(JSOP_DUP))                             // ITER RESULT RESULT
            return false;
        if (!emitAtomOp(cx->names().done, JSOP_GETPROP))  // ITER RESULT DONE
            return false;

        InternalIfEmitter ifDone(this);

        if (!ifDone.emitThen())                           // ITER RESULT
            return false;

        // Remove RESULT from the stack to release it.
        if (!emit1(JSOP_POP))                             // ITER
            return false;
        if (!emit1(JSOP_UNDEFINED))                       // ITER UNDEF
            return false;

        // If the iteration is done, leave loop here, instead of the branch at
        // the end of the loop.
        if (!loopInfo.emitSpecialBreakForDone(this))      // ITER UNDEF
            return false;

        if (!ifDone.emitEnd())                            // ITER RESULT
            return false;

        // Emit code to assign result.value to the iteration variable.
        //
        // Note that ES 13.7.5.13, step 5.c says getting result.value does not
        // call IteratorClose, so start JSTRY_ITERCLOSE after the GETPROP.
        if (!emitAtomOp(cx->names().value, JSOP_GETPROP)) // ITER VALUE
            return false;

        if (!loopInfo.emitBeginCodeNeedingIteratorClose(this))
            return false;

        if (!emitInitializeForInOrOfTarget(forOfHead))    // ITER VALUE
            return false;

        MOZ_ASSERT(stackDepth == loopDepth,
                   "the stack must be balanced around the initializing "
                   "operation");

        // Remove VALUE from the stack to release it.
        if (!emit1(JSOP_POP))                             // ITER
            return false;
        if (!emit1(JSOP_UNDEFINED))                       // ITER UNDEF
            return false;

        // Perform the loop body.
        ParseNode* forBody = forOfLoop->pn_right;
        if (!emitTree(forBody))                           // ITER UNDEF
            return false;

        MOZ_ASSERT(stackDepth == loopDepth,
                   "the stack must be balanced around the for-of body");

        if (!loopInfo.emitEndCodeNeedingIteratorClose(this))
            return false;

        // Set offset for continues.
        loopInfo.continueTarget = { offset() };

        if (!emitLoopEntry(forHeadExpr, initialJump))     // ITER UNDEF
            return false;

        if (!emit1(JSOP_FALSE))                           // ITER UNDEF FALSE
            return false;
        if (!emitBackwardJump(JSOP_IFEQ, top, &beq, &breakTarget))
            return false;                                 // ITER UNDEF

        MOZ_ASSERT(this->stackDepth == loopDepth);
    }

    // Let Ion know where the closing jump of this loop is.
    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - initialJump.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    if (!tryNoteList.append(JSTRY_FOR_OF, stackDepth, top.offset, breakTarget.offset))
        return false;

    return emitPopN(2);                                   //
}

bool
BytecodeEmitter::emitForIn(ParseNode* forInLoop, EmitterScope* headLexicalEmitterScope)
{
    MOZ_ASSERT(forInLoop->isKind(ParseNodeKind::For));
    MOZ_ASSERT(forInLoop->isArity(PN_BINARY));
    MOZ_ASSERT(forInLoop->isOp(JSOP_ITER));

    ParseNode* forInHead = forInLoop->pn_left;
    MOZ_ASSERT(forInHead->isKind(ParseNodeKind::ForIn));
    MOZ_ASSERT(forInHead->isArity(PN_TERNARY));

    // Annex B: Evaluate the var-initializer expression if present.
    // |for (var i = initializer in expr) { ... }|
    ParseNode* forInTarget = forInHead->pn_kid1;
    if (parser.isDeclarationList(forInTarget)) {
        ParseNode* decl = parser.singleBindingFromDeclaration(forInTarget);
        if (decl->isKind(ParseNodeKind::Name)) {
            if (ParseNode* initializer = decl->expr()) {
                MOZ_ASSERT(forInTarget->isKind(ParseNodeKind::Var),
                           "for-in initializers are only permitted for |var| declarations");

                if (!updateSourceCoordNotes(decl->pn_pos.begin))
                    return false;

                NameOpEmitter noe(this, decl->name(), NameOpEmitter::Kind::Initialize);
                if (!noe.prepareForRhs()) {
                    return false;
                }
                if (!emitInitializer(initializer, decl)) {
                    return false;
                }
                if (!noe.emitAssignment()) {
                    return false;
                }

                // Pop the initializer.
                if (!emit1(JSOP_POP)) {
                    return false;
                }
            }
        }
    }

    // Evaluate the expression being iterated.
    ParseNode* expr = forInHead->pn_kid3;
    if (!emitTreeInBranch(expr))                          // EXPR
        return false;

    // Convert the value to the appropriate sort of iterator object for the
    // loop variant (for-in, for-each-in, or destructuring for-in).
    unsigned iflags = forInLoop->pn_iflags;
    MOZ_ASSERT(0 == (iflags & ~(JSITER_FOREACH | JSITER_ENUMERATE)));
    if (!emit2(JSOP_ITER, AssertedCast<uint8_t>(iflags))) // ITER
        return false;

    // For-in loops have both the iterator and the value on the stack. Push
    // undefined to balance the stack.
    if (!emit1(JSOP_UNDEFINED))                           // ITER ITERVAL
        return false;

    LoopControl loopInfo(this, StatementKind::ForInLoop);

    /* Annotate so IonMonkey can find the loop-closing jump. */
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR_IN, &noteIndex))
        return false;

    // Jump down to the loop condition to minimize overhead (assuming at least
    // one iteration, just like the other loop forms).
    JumpList initialJump;
    if (!emitJump(JSOP_GOTO, &initialJump))               // ITER ITERVAL
        return false;

    JumpTarget top{ -1 };
    if (!emitLoopHead(nullptr, &top))                     // ITER ITERVAL
        return false;

    // If the loop had an escaping lexical declaration, replace the current
    // environment with an dead zoned one to implement TDZ semantics.
    if (headLexicalEmitterScope) {
        // The environment chain only includes an environment for the for-in
        // loop head *if* a scope binding is captured, thereby requiring
        // recreation each iteration. If a lexical scope exists for the head,
        // it must be the innermost one. If that scope has closed-over
        // bindings inducing an environment, recreate the current environment.
        MOZ_ASSERT(forInTarget->isKind(ParseNodeKind::Let) ||
                   forInTarget->isKind(ParseNodeKind::Const));
        MOZ_ASSERT(headLexicalEmitterScope == innermostEmitterScope());
        MOZ_ASSERT(headLexicalEmitterScope->scope(this)->kind() == ScopeKind::Lexical);

        if (headLexicalEmitterScope->hasEnvironment()) {
            if (!emit1(JSOP_RECREATELEXICALENV))          // ITER ITERVAL
                return false;
        }

        // For uncaptured bindings, put them back in TDZ.
        if (!headLexicalEmitterScope->deadZoneFrameSlots(this))
            return false;
    }

    {
#ifdef DEBUG
        auto loopDepth = this->stackDepth;
#endif
        MOZ_ASSERT(loopDepth >= 2);

        if (iflags == JSITER_ENUMERATE) {
            if (!emit1(JSOP_ITERNEXT))                    // ITER ITERVAL
                return false;
        }

        if (!emitInitializeForInOrOfTarget(forInHead))    // ITER ITERVAL
            return false;

        MOZ_ASSERT(this->stackDepth == loopDepth,
                   "iterator and iterval must be left on the stack");
    }

    // Perform the loop body.
    ParseNode* forBody = forInLoop->pn_right;
    if (!emitTree(forBody))                               // ITER ITERVAL
        return false;

    // Set offset for continues.
    loopInfo.continueTarget = { offset() };

    // Make sure this code is attributed to the "for".
    if (!updateSourceCoordNotes(forInHead->pn_pos.begin))
        return false;

    if (!emitLoopEntry(nullptr, initialJump))             // ITER ITERVAL
        return false;
    if (!emit1(JSOP_POP))                                 // ITER
        return false;
    if (!emit1(JSOP_MOREITER))                            // ITER NEXTITERVAL?
        return false;
    if (!emit1(JSOP_ISNOITER))                            // ITER NEXTITERVAL? ISNOITER
        return false;

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(JSOP_IFEQ, top, &beq, &breakTarget))
        return false;                                     // ITER NEXTITERVAL

    // Set the srcnote offset so we can find the closing jump.
    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - initialJump.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    // Pop the enumeration value.
    if (!emit1(JSOP_POP))                                 // ITER
        return false;

    if (!tryNoteList.append(JSTRY_FOR_IN, this->stackDepth, top.offset, offset()))
        return false;

    return emit1(JSOP_ENDITER);                           //
}

/* C-style `for (init; cond; update) ...` loop. */
bool
BytecodeEmitter::emitCStyleFor(ParseNode* pn, EmitterScope* headLexicalEmitterScope)
{
    LoopControl loopInfo(this, StatementKind::ForLoop);

    ParseNode* forHead = pn->pn_left;
    ParseNode* forBody = pn->pn_right;

    // If the head of this for-loop declared any lexical variables, the parser
    // wrapped this ParseNodeKind::For node in a ParseNodeKind::LexicalScope
    // representing the implicit scope of those variables. By the time we get here,
    // we have already entered that scope. So far, so good.
    //
    // ### Scope freshening
    //
    // Each iteration of a `for (let V...)` loop creates a fresh loop variable
    // binding for V, even if the loop is a C-style `for(;;)` loop:
    //
    //     var funcs = [];
    //     for (let i = 0; i < 2; i++)
    //         funcs.push(function() { return i; });
    //     assertEq(funcs[0](), 0);  // the two closures capture...
    //     assertEq(funcs[1](), 1);  // ...two different `i` bindings
    //
    // This is implemented by "freshening" the implicit block -- changing the
    // scope chain to a fresh clone of the instantaneous block object -- each
    // iteration, just before evaluating the "update" in for(;;) loops.
    //
    // No freshening occurs in `for (const ...;;)` as there's no point: you
    // can't reassign consts. This is observable through the Debugger API. (The
    // ES6 spec also skips cloning the environment in this case.)
    bool forLoopRequiresFreshening = false;
    if (ParseNode* init = forHead->pn_kid1) {
        // Emit the `init` clause, whether it's an expression or a variable
        // declaration. (The loop variables were hoisted into an enclosing
        // scope, but we still need to emit code for the initializers.)
        if (!updateSourceCoordNotes(init->pn_pos.begin))
            return false;
        if (init->isForLoopDeclaration()) {
            if (!emitTree(init))
                return false;
        } else {
            // 'init' is an expression, not a declaration. emitTree left its
            // value on the stack.
            if (!emitTree(init, ValueUsage::IgnoreValue))
                return false;
            if (!emit1(JSOP_POP))
                return false;
        }

        // ES 13.7.4.8 step 2. The initial freshening.
        //
        // If an initializer let-declaration may be captured during loop iteration,
        // the current scope has an environment.  If so, freshen the current
        // environment to expose distinct bindings for each loop iteration.
        forLoopRequiresFreshening = init->isKind(ParseNodeKind::Let) && headLexicalEmitterScope;
        if (forLoopRequiresFreshening) {
            // The environment chain only includes an environment for the for(;;)
            // loop head's let-declaration *if* a scope binding is captured, thus
            // requiring a fresh environment each iteration. If a lexical scope
            // exists for the head, it must be the innermost one. If that scope
            // has closed-over bindings inducing an environment, recreate the
            // current environment.
            MOZ_ASSERT(headLexicalEmitterScope == innermostEmitterScope());
            MOZ_ASSERT(headLexicalEmitterScope->scope(this)->kind() == ScopeKind::Lexical);

            if (headLexicalEmitterScope->hasEnvironment()) {
                if (!emit1(JSOP_FRESHENLEXICALENV))
                    return false;
            }
        }
    }

    /*
     * NB: the SRC_FOR note has offsetBias 1 (JSOP_NOP_LENGTH).
     * Use tmp to hold the biased srcnote "top" offset, which differs
     * from the top local variable by the length of the JSOP_GOTO
     * emitted in between tmp and top if this loop has a condition.
     */
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR, &noteIndex))
        return false;
    if (!emit1(JSOP_NOP))
        return false;
    ptrdiff_t tmp = offset();

    JumpList jmp;
    if (forHead->pn_kid2) {
        /* Goto the loop condition, which branches back to iterate. */
        if (!emitJump(JSOP_GOTO, &jmp))
            return false;
    }

    /* Emit code for the loop body. */
    JumpTarget top{ -1 };
    if (!emitLoopHead(forBody, &top))
        return false;
    if (jmp.offset == -1 && !emitLoopEntry(forBody, jmp))
        return false;

    if (!emitTreeInBranch(forBody))
        return false;

    // Set loop and enclosing "update" offsets, for continue.  Note that we
    // continue to immediately *before* the block-freshening: continuing must
    // refresh the block.
    if (!emitJumpTarget(&loopInfo.continueTarget))
        return false;

    // ES 13.7.4.8 step 3.e. The per-iteration freshening.
    if (forLoopRequiresFreshening) {
        MOZ_ASSERT(headLexicalEmitterScope == innermostEmitterScope());
        MOZ_ASSERT(headLexicalEmitterScope->scope(this)->kind() == ScopeKind::Lexical);

        if (headLexicalEmitterScope->hasEnvironment()) {
            if (!emit1(JSOP_FRESHENLEXICALENV))
                return false;
        }
    }

    // Check for update code to do before the condition (if any).
    // The update code may not be executed at all; it needs its own TDZ cache.
    if (ParseNode* update = forHead->pn_kid3) {
        TDZCheckCache tdzCache(this);

        if (!updateSourceCoordNotes(update->pn_pos.begin))
            return false;
        if (!emitTree(update, ValueUsage::IgnoreValue))
            return false;
        if (!emit1(JSOP_POP))
            return false;

        /* Restore the absolute line number for source note readers. */
        uint32_t lineNum = parser.tokenStream().srcCoords.lineNum(pn->pn_pos.end);
        if (currentLine() != lineNum) {
            if (!newSrcNote2(SRC_SETLINE, ptrdiff_t(lineNum)))
                return false;
            current->currentLine = lineNum;
            current->lastColumn = 0;
        }
    }

    ptrdiff_t tmp3 = offset();

    if (forHead->pn_kid2) {
        /* Fix up the goto from top to target the loop condition. */
        MOZ_ASSERT(jmp.offset >= 0);
        if (!emitLoopEntry(forHead->pn_kid2, jmp))
            return false;

        if (!emitTree(forHead->pn_kid2))
            return false;
    } else if (!forHead->pn_kid3) {
        // If there is no condition clause and no update clause, mark
        // the loop-ending "goto" with the location of the "for".
        // This ensures that the debugger will stop on each loop
        // iteration.
        if (!updateSourceCoordNotes(pn->pn_pos.begin))
            return false;
    }

    /* Set the first note offset so we can find the loop condition. */
    if (!setSrcNoteOffset(noteIndex, 0, tmp3 - tmp))
        return false;
    if (!setSrcNoteOffset(noteIndex, 1, loopInfo.continueTarget.offset - tmp))
        return false;

    /* If no loop condition, just emit a loop-closing jump. */
    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(forHead->pn_kid2 ? JSOP_IFNE : JSOP_GOTO, top, &beq, &breakTarget))
        return false;

    /* The third note offset helps us find the loop-closing jump. */
    if (!setSrcNoteOffset(noteIndex, 2, beq.offset - tmp))
        return false;

    if (!tryNoteList.append(JSTRY_LOOP, stackDepth, top.offset, breakTarget.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    return true;
}

bool
BytecodeEmitter::emitFor(ParseNode* pn, EmitterScope* headLexicalEmitterScope)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::For));

    if (pn->pn_left->isKind(ParseNodeKind::ForHead))
        return emitCStyleFor(pn, headLexicalEmitterScope);

    if (!updateLineNumberNotes(pn->pn_pos.begin))
        return false;

    if (pn->pn_left->isKind(ParseNodeKind::ForIn))
        return emitForIn(pn, headLexicalEmitterScope);

    MOZ_ASSERT(pn->pn_left->isKind(ParseNodeKind::ForOf));
    return emitForOf(pn, headLexicalEmitterScope);
}

bool
BytecodeEmitter::emitComprehensionForInOrOfVariables(ParseNode* pn, bool* lexicalScope)
{
    // ES6 specifies that lexical for-loop variables get a fresh binding each
    // iteration, and that evaluation of the expression looped over occurs with
    // these variables dead zoned.  But these rules only apply to *standard*
    // for-in/of loops, and we haven't extended these requirements to
    // comprehension syntax.

    *lexicalScope = pn->isKind(ParseNodeKind::LexicalScope);
    if (*lexicalScope) {
        // This is initially-ES7-tracked syntax, now with considerably murkier
        // outlook. The scope work is done by the caller by instantiating an
        // EmitterScope. There's nothing to do here.
    } else {
        // This is legacy comprehension syntax.  We'll haveParseNodeKind::Let here, using
        // a lexical scope provided by/for the entire comprehension.  Name
        // analysis assumes declarations initialize lets, but as we're handling
        // this declaration manually, we must also initialize manually to avoid
        // triggering dead zone checks.
        MOZ_ASSERT(pn->isKind(ParseNodeKind::Let));
        MOZ_ASSERT(pn->pn_count == 1);

        if (!emitDeclarationList(pn))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitComprehensionForOf(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::ComprehensionFor));

    ParseNode* forHead = pn->pn_left;
    MOZ_ASSERT(forHead->isKind(ParseNodeKind::ForOf));

    ParseNode* forHeadExpr = forHead->pn_kid3;
    ParseNode* forBody = pn->pn_right;

    ParseNode* loopDecl = forHead->pn_kid1;
    bool lexicalScope = false;
    if (!emitComprehensionForInOrOfVariables(loopDecl, &lexicalScope))
        return false;

    // For-of loops run with two values on the stack: the iterator and the
    // current result object.

    // Evaluate the expression to the right of 'of'.
    if (!emitTree(forHeadExpr))                // EXPR
        return false;
    if (!emitIterator())                       // ITER
        return false;

    // Push a dummy result so that we properly enter iteration midstream.
    if (!emit1(JSOP_UNDEFINED))                // ITER VALUE
        return false;

    // Enter the block before the loop body, after evaluating the obj.
    // Initialize let bindings with undefined when entering, as the name
    // assigned to is a plain assignment.
    TDZCheckCache tdzCache(this);
    Maybe<EmitterScope> emitterScope;
    ParseNode* loopVariableName;
    if (lexicalScope) {
        loopVariableName = parser.singleBindingFromDeclaration(loopDecl->pn_expr);
        emitterScope.emplace(this);
        if (!emitterScope->enterComprehensionFor(this, loopDecl->scopeBindings()))
            return false;
    } else {
        loopVariableName = parser.singleBindingFromDeclaration(loopDecl);
    }

    LoopControl loopInfo(this, StatementKind::ForOfLoop);

    // Jump down to the loop condition to minimize overhead assuming at least
    // one iteration, as the other loop forms do.  Annotate so IonMonkey can
    // find the loop-closing jump.
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR_OF, &noteIndex))
        return false;
    JumpList jmp;
    if (!emitJump(JSOP_GOTO, &jmp))
        return false;

    JumpTarget top{ -1 };
    if (!emitLoopHead(nullptr, &top))
        return false;

#ifdef DEBUG
    int loopDepth = this->stackDepth;
#endif

    if (!emit1(JSOP_POP))                                 // ITER
        return false;
    if (!emit1(JSOP_DUP))                                 // ITER ITER
        return false;
    if (!emitIteratorNext(forHead))                       // ITER RESULT
        return false;
    if (!emit1(JSOP_DUP))                                 // ITER RESULT RESULT
        return false;
    if (!emitAtomOp(cx->names().done, JSOP_GETPROP))      // ITER RESULT DONE
        return false;

    InternalIfEmitter ifDone(this);

    if (!ifDone.emitThen())                               // ITER RESULT
        return false;

    // Remove RESULT from the stack to release it.
    if (!emit1(JSOP_POP))                                 // ITER
        return false;
    if (!emit1(JSOP_UNDEFINED))                           // ITER UNDEF
        return false;

    // If the iteration is done, leave loop here, instead of the branch at
    // the end of the loop.
    if (!loopInfo.emitSpecialBreakForDone(this))          // ITER UNDEF
        return false;

    if (!ifDone.emitEnd())                                // ITER RESULT
        return false;

    // Emit code to assign result.value to the iteration variable.
    if (!emitAtomOp(cx->names().value, JSOP_GETPROP))     // ITER VALUE
        return false;

    // Notice: Comprehension for-of doesn't perform IteratorClose, since it's
    // not in the spec.
    if (!emitAssignment(loopVariableName, JSOP_NOP, nullptr)) // ITER VALUE
        return false;

    // Remove VALUE from the stack to release it.
    if (!emit1(JSOP_POP))                                 // ITER
        return false;
    if (!emit1(JSOP_UNDEFINED))                           // ITER UNDEF
        return false;

    // The stack should be balanced around the assignment opcode sequence.
    MOZ_ASSERT(this->stackDepth == loopDepth);

    // Emit code for the loop body.
    if (!emitTree(forBody))                               // ITER UNDEF
        return false;

    // The stack should be balanced around the assignment opcode sequence.
    MOZ_ASSERT(this->stackDepth == loopDepth);

    // Set offset for continues.
    loopInfo.continueTarget = { offset() };

    if (!emitLoopEntry(forHeadExpr, jmp))
        return false;

    if (!emit1(JSOP_FALSE))                               // ITER VALUE FALSE
        return false;

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(JSOP_IFEQ, top, &beq, &breakTarget))
        return false;                                     // ITER VALUE

    MOZ_ASSERT(this->stackDepth == loopDepth);

    // Let Ion know where the closing jump of this loop is.
    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - jmp.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    if (!tryNoteList.append(JSTRY_FOR_OF, stackDepth, top.offset, breakTarget.offset))
        return false;

    if (emitterScope) {
        if (!emitterScope->leave(this))
            return false;
        emitterScope.reset();
    }

    // Pop the result and the iter.
    return emitPopN(2);                                   //
}

bool
BytecodeEmitter::emitComprehensionForIn(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::ComprehensionFor));

    ParseNode* forHead = pn->pn_left;
    MOZ_ASSERT(forHead->isKind(ParseNodeKind::ForIn));

    ParseNode* forBody = pn->pn_right;

    ParseNode* loopDecl = forHead->pn_kid1;
    bool lexicalScope = false;
    if (loopDecl && !emitComprehensionForInOrOfVariables(loopDecl, &lexicalScope))
        return false;

    // Evaluate the expression to the right of 'in'.
    if (!emitTree(forHead->pn_kid3))
        return false;

    /*
     * Emit a bytecode to convert top of stack value to the iterator
     * object depending on the loop variant (for-in, for-each-in, or
     * destructuring for-in).
     */
    MOZ_ASSERT(pn->isOp(JSOP_ITER));
    if (!emit2(JSOP_ITER, (uint8_t) pn->pn_iflags))
        return false;

    // For-in loops have both the iterator and the value on the stack. Push
    // undefined to balance the stack.
    if (!emit1(JSOP_UNDEFINED))
        return false;

    // Enter the block before the loop body, after evaluating the obj.
    // Initialize let bindings with undefined when entering, as the name
    // assigned to is a plain assignment.
    TDZCheckCache tdzCache(this);
    Maybe<EmitterScope> emitterScope;
    if (lexicalScope) {
        emitterScope.emplace(this);
        if (!emitterScope->enterComprehensionFor(this, loopDecl->scopeBindings()))
            return false;
    }

    LoopControl loopInfo(this, StatementKind::ForInLoop);

    /* Annotate so IonMonkey can find the loop-closing jump. */
    unsigned noteIndex;
    if (!newSrcNote(SRC_FOR_IN, &noteIndex))
        return false;

    /*
     * Jump down to the loop condition to minimize overhead assuming at
     * least one iteration, as the other loop forms do.
     */
    JumpList jmp;
    if (!emitJump(JSOP_GOTO, &jmp))
        return false;

    JumpTarget top{ -1 };
    if (!emitLoopHead(nullptr, &top))
        return false;

#ifdef DEBUG
    int loopDepth = this->stackDepth;
#endif

    // Emit code to assign the enumeration value to the left hand side, but
    // also leave it on the stack.
    if (!emitAssignment(forHead->pn_kid2, JSOP_NOP, nullptr))
        return false;

    /* The stack should be balanced around the assignment opcode sequence. */
    MOZ_ASSERT(this->stackDepth == loopDepth);

    /* Emit code for the loop body. */
    if (!emitTree(forBody))
        return false;

    // Set offset for continues.
    loopInfo.continueTarget = { offset() };

    if (!emitLoopEntry(nullptr, jmp))
        return false;
    if (!emit1(JSOP_POP))
        return false;
    if (!emit1(JSOP_MOREITER))
        return false;
    if (!emit1(JSOP_ISNOITER))
        return false;
    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(JSOP_IFEQ, top, &beq, &breakTarget))
        return false;

    /* Set the srcnote offset so we can find the closing jump. */
    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - jmp.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    // Pop the enumeration value.
    if (!emit1(JSOP_POP))
        return false;

    JumpTarget endIter{ offset() };
    if (!tryNoteList.append(JSTRY_FOR_IN, this->stackDepth, top.offset, endIter.offset))
        return false;
    if (!emit1(JSOP_ENDITER))
        return false;

    if (emitterScope) {
        if (!emitterScope->leave(this))
            return false;
        emitterScope.reset();
    }

    return true;
}

bool
BytecodeEmitter::emitComprehensionFor(ParseNode* compFor)
{
    MOZ_ASSERT(compFor->pn_left->isKind(ParseNodeKind::ForIn) ||
               compFor->pn_left->isKind(ParseNodeKind::ForOf));

    if (!updateLineNumberNotes(compFor->pn_pos.begin))
        return false;

    return compFor->pn_left->isKind(ParseNodeKind::ForIn)
           ? emitComprehensionForIn(compFor)
           : emitComprehensionForOf(compFor);
}

MOZ_NEVER_INLINE bool
BytecodeEmitter::emitFunction(ParseNode* pn, bool needsProto)
{
    FunctionBox* funbox = pn->pn_funbox;
    RootedFunction fun(cx, funbox->function());
    RootedAtom name(cx, fun->explicitName());
    MOZ_ASSERT_IF(fun->isInterpretedLazy(), fun->lazyScript());

    /*
     * Set the |wasEmitted| flag in the funbox once the function has been
     * emitted. Function definitions that need hoisting to the top of the
     * function will be seen by emitFunction in two places.
     */
    if (funbox->wasEmitted) {
        // Annex B block-scoped functions are hoisted like any other
        // block-scoped function to the top of their scope. When their
        // definitions are seen for the second time, we need to emit the
        // assignment that assigns the function to the outer 'var' binding.
        if (funbox->isAnnexB) {
            // Get the location of the 'var' binding in the body scope. The
            // name must be found, else there is a bug in the Annex B handling
            // in Parser.
            //
            // In sloppy eval contexts, this location is dynamic.
            Maybe<NameLocation> lhsLoc = locationOfNameBoundInScope(name, varEmitterScope);

            // If there are parameter expressions, the var name could be a
            // parameter.
            if (!lhsLoc && sc->isFunctionBox() && sc->asFunctionBox()->hasExtraBodyVarScope())
                lhsLoc = locationOfNameBoundInScope(name, varEmitterScope->enclosingInFrame());

            if (!lhsLoc) {
                lhsLoc = Some(NameLocation::DynamicAnnexBVar());
            } else {
                MOZ_ASSERT(lhsLoc->bindingKind() == BindingKind::Var ||
                           lhsLoc->bindingKind() == BindingKind::FormalParameter ||
                           (lhsLoc->bindingKind() == BindingKind::Let &&
                            sc->asFunctionBox()->hasParameterExprs));
            }

            NameOpEmitter noe(this, name, *lhsLoc, NameOpEmitter::Kind::SimpleAssignment);
            if (!noe.prepareForRhs()) {
                return false;
            }
            if (!emitGetName(name)) {
                return false;
            }
            if (!noe.emitAssignment()) {
                return false;
            }
            if (!emit1(JSOP_POP)) {
                return false;
            }
        }

        MOZ_ASSERT_IF(fun->hasScript(), fun->nonLazyScript());
        MOZ_ASSERT(pn->functionIsHoisted());
        return true;
    }

    funbox->wasEmitted = true;

    /*
     * Mark as singletons any function which will only be executed once, or
     * which is inner to a lambda we only expect to run once. In the latter
     * case, if the lambda runs multiple times then CloneFunctionObject will
     * make a deep clone of its contents.
     */
    if (fun->isInterpreted()) {
        bool singleton = checkRunOnceContext();
        if (!JSFunction::setTypeForScriptedFunction(cx, fun, singleton))
            return false;

        SharedContext* outersc = sc;
        if (fun->isInterpretedLazy()) {
            // We need to update the static scope chain regardless of whether
            // the LazyScript has already been initialized, due to the case
            // where we previously successfully compiled an inner function's
            // lazy script but failed to compile the outer script after the
            // fact. If we attempt to compile the outer script again, the
            // static scope chain will be newly allocated and will mismatch
            // the previously compiled LazyScript's.
            ScriptSourceObject* source = &script->sourceObject()->as<ScriptSourceObject>();
            fun->lazyScript()->setEnclosingScopeAndSource(innermostScope(), source);
            if (emittingRunOnceLambda)
                fun->lazyScript()->setTreatAsRunOnce();
        } else {
            MOZ_ASSERT_IF(outersc->strict(), funbox->strictScript);

            // Inherit most things (principals, version, etc) from the
            // parent.  Use default values for the rest.
            Rooted<JSScript*> parent(cx, script);
            MOZ_ASSERT(parent->getVersion() == parser.options().version);
            MOZ_ASSERT(parent->mutedErrors() == parser.options().mutedErrors());
            const TransitiveCompileOptions& transitiveOptions = parser.options();
            CompileOptions options(cx, transitiveOptions);

            Rooted<ScriptSourceObject*> sourceObject(cx, script->sourceObject());
            Rooted<JSScript*> script(cx, JSScript::Create(cx, options, sourceObject,
                                                          funbox->bufStart, funbox->bufEnd,
                                                          funbox->toStringStart,
                                                          funbox->toStringEnd));
            if (!script)
                return false;

            BytecodeEmitter bce2(this, parser, funbox, script, /* lazyScript = */ nullptr,
                                 pn->pn_pos, emitterMode);
            if (!bce2.init())
                return false;

            /* We measured the max scope depth when we parsed the function. */
            if (!bce2.emitFunctionScript(pn->pn_body))
                return false;

            if (funbox->isLikelyConstructorWrapper())
                script->setLikelyConstructorWrapper();
        }

        if (outersc->isFunctionBox())
            outersc->asFunctionBox()->setHasInnerFunctions();
    } else {
        MOZ_ASSERT(IsAsmJSModule(fun));
    }

    /* Make the function object a literal in the outer script's pool. */
    unsigned index = objectList.add(pn->pn_funbox);

    /* Non-hoisted functions simply emit their respective op. */
    if (!pn->functionIsHoisted()) {
        /* JSOP_LAMBDA_ARROW is always preceded by a new.target */
        MOZ_ASSERT(fun->isArrow() == (pn->getOp() == JSOP_LAMBDA_ARROW));
        if (funbox->isAsync()) {
            MOZ_ASSERT(!needsProto);
            return emitAsyncWrapper(index, funbox->needsHomeObject(), fun->isArrow(),
                                    fun->isStarGenerator());
        }

        if (fun->isArrow()) {
            if (sc->allowNewTarget()) {
                if (!emit1(JSOP_NEWTARGET))
                    return false;
            } else {
                if (!emit1(JSOP_NULL))
                    return false;
            }
        }

        if (needsProto) {
            MOZ_ASSERT(pn->getOp() == JSOP_LAMBDA);
            pn->setOp(JSOP_FUNWITHPROTO);
        }

        if (pn->getOp() == JSOP_DEFFUN) {
            if (!emitIndex32(JSOP_LAMBDA, index))
                return false;
            return emit1(JSOP_DEFFUN);
        }

        return emitIndex32(pn->getOp(), index);
    }

    MOZ_ASSERT(!needsProto);

    bool topLevelFunction;
    if (sc->isFunctionBox() || (sc->isEvalContext() && sc->strict())) {
        // No nested functions inside other functions are top-level.
        topLevelFunction = false;
    } else {
        // In sloppy eval scripts, top-level functions in are accessed
        // dynamically. In global and module scripts, top-level functions are
        // those bound in the var scope.
        NameLocation loc = lookupName(name);
        topLevelFunction = loc.kind() == NameLocation::Kind::Dynamic ||
                           loc.bindingKind() == BindingKind::Var;
    }

    if (topLevelFunction) {
        if (sc->isModuleContext()) {
            // For modules, we record the function and instantiate the binding
            // during ModuleInstantiate(), before the script is run.

            RootedModuleObject module(cx, sc->asModuleContext()->module());
            if (!module->noteFunctionDeclaration(cx, name, fun))
                return false;
        } else {
            MOZ_ASSERT(sc->isGlobalContext() || sc->isEvalContext());
            MOZ_ASSERT(pn->getOp() == JSOP_NOP);
            switchToPrologue();
            if (funbox->isAsync()) {
                if (!emitAsyncWrapper(index, fun->isMethod(), fun->isArrow(),
                                      fun->isStarGenerator()))
                {
                    return false;
                }
            } else {
                if (!emitIndex32(JSOP_LAMBDA, index))
                    return false;
            }
            if (!emit1(JSOP_DEFFUN))
                return false;
            if (!updateSourceCoordNotes(pn->pn_pos.begin))
                return false;
            switchToMain();
        }
    } else {
        // For functions nested within functions and blocks, make a lambda and
        // initialize the binding name of the function in the current scope.

        NameOpEmitter noe(this, name, NameOpEmitter::Kind::Initialize);
        if (!noe.prepareForRhs()) {
            return false;
        }
        if (funbox->isAsync()) {
            if (!emitAsyncWrapper(index, /* needsHomeObject = */ false,
                                  /* isArrow = */ false, funbox->isStarGenerator()))
            {
                return false;
            }
        } else {
            if (!emitIndexOp(JSOP_LAMBDA, index)) {
                return false;
            }
        }
        if (!noe.emitAssignment()) {
            return false;
        }
        if (!emit1(JSOP_POP)) {
            return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitAsyncWrapperLambda(unsigned index, bool isArrow) {
    if (isArrow) {
        if (sc->allowNewTarget()) {
            if (!emit1(JSOP_NEWTARGET))
                return false;
        } else {
            if (!emit1(JSOP_NULL))
                return false;
        }
        if (!emitIndex32(JSOP_LAMBDA_ARROW, index))
            return false;
    } else {
        if (!emitIndex32(JSOP_LAMBDA, index))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitAsyncWrapper(unsigned index, bool needsHomeObject, bool isArrow,
                                  bool isStarGenerator)
{
    // needsHomeObject can be true for propertyList for extended class.
    // In that case push both unwrapped and wrapped function, in order to
    // initialize home object of unwrapped function, and set wrapped function
    // as a property.
    //
    //   lambda       // unwrapped
    //   dup          // unwrapped unwrapped
    //   toasync      // unwrapped wrapped
    //
    // Emitted code is surrounded by the following code.
    //
    //                    // classObj classCtor classProto
    //   (emitted code)   // classObj classCtor classProto unwrapped wrapped
    //   swap             // classObj classCtor classProto wrapped unwrapped
    //   dupat 2          // classObj classCtor classProto wrapped unwrapped classProto
    //   inithomeobject   // classObj classCtor classProto wrapped unwrapped
    //                    //   initialize the home object of unwrapped
    //                    //   with classProto here
    //   pop              // classObj classCtor classProto wrapped
    //   inithiddenprop   // classObj classCtor classProto wrapped
    //                    //   initialize the property of the classProto
    //                    //   with wrapped function here
    //   pop              // classObj classCtor classProto
    //
    // needsHomeObject is false for other cases, push wrapped function only.
    if (!emitAsyncWrapperLambda(index, isArrow))
        return false;
    if (needsHomeObject) {
        if (!emit1(JSOP_DUP))
            return false;
    }
    if (isStarGenerator) {
        if (!emit1(JSOP_TOASYNCGEN))
            return false;
    } else {
        if (!emit1(JSOP_TOASYNC))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::emitDo(ParseNode* pn)
{
    /* Emit an annotated nop so IonBuilder can recognize the 'do' loop. */
    unsigned noteIndex;
    if (!newSrcNote(SRC_WHILE, &noteIndex))
        return false;
    if (!emit1(JSOP_NOP))
        return false;

    unsigned noteIndex2;
    if (!newSrcNote(SRC_WHILE, &noteIndex2))
        return false;

    /* Compile the loop body. */
    JumpTarget top;
    if (!emitLoopHead(pn->pn_left, &top))
        return false;

    LoopControl loopInfo(this, StatementKind::DoLoop);

    JumpList empty;
    if (!emitLoopEntry(nullptr, empty))
        return false;

    if (!emitTree(pn->pn_left))
        return false;

    // Set the offset for continues.
    if (!emitJumpTarget(&loopInfo.continueTarget))
        return false;

    /* Compile the loop condition, now that continues know where to go. */
    if (!emitTree(pn->pn_right))
        return false;

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(JSOP_IFNE, top, &beq, &breakTarget))
        return false;

    if (!tryNoteList.append(JSTRY_LOOP, stackDepth, top.offset, breakTarget.offset))
        return false;

    /*
     * Update the annotations with the update and back edge positions, for
     * IonBuilder.
     *
     * Be careful: We must set noteIndex2 before noteIndex in case the noteIndex
     * note gets bigger.
     */
    if (!setSrcNoteOffset(noteIndex2, 0, beq.offset - top.offset))
        return false;
    if (!setSrcNoteOffset(noteIndex, 0, 1 + (loopInfo.continueTarget.offset - top.offset)))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    return true;
}

bool
BytecodeEmitter::emitWhile(ParseNode* pn)
{
    /*
     * Minimize bytecodes issued for one or more iterations by jumping to
     * the condition below the body and closing the loop if the condition
     * is true with a backward branch. For iteration count i:
     *
     *  i    test at the top                 test at the bottom
     *  =    ===============                 ==================
     *  0    ifeq-pass                       goto; ifne-fail
     *  1    ifeq-fail; goto; ifne-pass      goto; ifne-pass; ifne-fail
     *  2    2*(ifeq-fail; goto); ifeq-pass  goto; 2*ifne-pass; ifne-fail
     *  . . .
     *  N    N*(ifeq-fail; goto); ifeq-pass  goto; N*ifne-pass; ifne-fail
     */

    // If we have a single-line while, like "while (x) ;", we want to
    // emit the line note before the initial goto, so that the
    // debugger sees a single entry point.  This way, if there is a
    // breakpoint on the line, it will only fire once; and "next"ing
    // will skip the whole loop.  However, for the multi-line case we
    // want to emit the line note after the initial goto, so that
    // "cont" stops on each iteration -- but without a stop before the
    // first iteration.
    if (parser.tokenStream().srcCoords.lineNum(pn->pn_pos.begin) ==
        parser.tokenStream().srcCoords.lineNum(pn->pn_pos.end))
    {
        if (!updateSourceCoordNotes(pn->pn_pos.begin))
            return false;
    }

    JumpTarget top{ -1 };
    if (!emitJumpTarget(&top))
        return false;

    LoopControl loopInfo(this, StatementKind::WhileLoop);
    loopInfo.continueTarget = top;

    unsigned noteIndex;
    if (!newSrcNote(SRC_WHILE, &noteIndex))
        return false;

    JumpList jmp;
    if (!emitJump(JSOP_GOTO, &jmp))
        return false;

    if (!emitLoopHead(pn->pn_right, &top))
        return false;

    if (!emitTreeInBranch(pn->pn_right))
        return false;

    if (!emitLoopEntry(pn->pn_left, jmp))
        return false;
    if (!emitTree(pn->pn_left))
        return false;

    JumpList beq;
    JumpTarget breakTarget{ -1 };
    if (!emitBackwardJump(JSOP_IFNE, top, &beq, &breakTarget))
        return false;

    if (!tryNoteList.append(JSTRY_LOOP, stackDepth, top.offset, breakTarget.offset))
        return false;

    if (!setSrcNoteOffset(noteIndex, 0, beq.offset - jmp.offset))
        return false;

    if (!loopInfo.patchBreaksAndContinues(this))
        return false;

    return true;
}

bool
BytecodeEmitter::emitBreak(PropertyName* label)
{
    BreakableControl* target;
    SrcNoteType noteType;
    if (label) {
        // Any statement with the matching label may be the break target.
        auto hasSameLabel = [label](LabelControl* labelControl) {
            return labelControl->label() == label;
        };
        target = findInnermostNestableControl<LabelControl>(hasSameLabel);
        noteType = SRC_BREAK2LABEL;
    } else {
        auto isNotLabel = [](BreakableControl* control) {
            return !control->is<LabelControl>();
        };
        target = findInnermostNestableControl<BreakableControl>(isNotLabel);
        noteType = (target->kind() == StatementKind::Switch) ? SRC_SWITCHBREAK : SRC_BREAK;
    }

    return emitGoto(target, &target->breaks, noteType);
}

bool
BytecodeEmitter::emitContinue(PropertyName* label)
{
    LoopControl* target = nullptr;
    if (label) {
        // Find the loop statement enclosed by the matching label.
        NestableControl* control = innermostNestableControl;
        while (!control->is<LabelControl>() || control->as<LabelControl>().label() != label) {
            if (control->is<LoopControl>())
                target = &control->as<LoopControl>();
            control = control->enclosing();
        }
    } else {
        target = findInnermostNestableControl<LoopControl>();
    }
    return emitGoto(target, &target->continues, SRC_CONTINUE);
}

bool
BytecodeEmitter::emitGetFunctionThis(ParseNode* pn)
{
    MOZ_ASSERT(sc->thisBinding() == ThisBinding::Function);
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Name));
    MOZ_ASSERT(pn->name() == cx->names().dotThis);

    return emitGetFunctionThis(Some(pn->pn_pos.begin));
}

bool
BytecodeEmitter::emitGetFunctionThis(const mozilla::Maybe<uint32_t>& offset)
{
    if (offset) {
        if (!updateLineNumberNotes(*offset)) {
            return false;
        }
    }

    if (!emitGetName(cx->names().dotThis)) {              // THIS
        return false;
    }
    if (sc->needsThisTDZChecks()) {
        if (!emit1(JSOP_CHECKTHIS)) {                     // THIS
            return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitGetThisForSuperBase(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::SuperBase));
    return emitGetFunctionThis(pn->pn_kid);               // THIS
}

bool
BytecodeEmitter::emitThisLiteral(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::This));

    if (ParseNode* thisName = pn->pn_kid) {
        return emitGetFunctionThis(thisName);             // THIS
    }

    if (sc->thisBinding() == ThisBinding::Module) {
        return emit1(JSOP_UNDEFINED);                     // UNDEF
    }

    MOZ_ASSERT(sc->thisBinding() == ThisBinding::Global);
    return emit1(JSOP_GLOBALTHIS);                        // THIS
}

bool
BytecodeEmitter::emitCheckDerivedClassConstructorReturn()
{
    MOZ_ASSERT(lookupName(cx->names().dotThis).hasKnownSlot());
    if (!emitGetName(cx->names().dotThis))
        return false;
    if (!emit1(JSOP_CHECKRETURN))
        return false;
    return true;
}

bool
BytecodeEmitter::emitReturn(ParseNode* pn)
{
    if (!updateSourceCoordNotes(pn->pn_pos.begin))
        return false;

    bool needsIteratorResult = sc->isFunctionBox() && sc->asFunctionBox()->needsIteratorResult();
    if (needsIteratorResult) {
        if (!emitPrepareIteratorResult())
            return false;
    }

    /* Push a return value */
    if (ParseNode* pn2 = pn->pn_kid) {
        if (!emitTree(pn2))
            return false;

        bool isAsyncGenerator = sc->asFunctionBox()->isAsync() &&
                                sc->asFunctionBox()->isStarGenerator();
        if (isAsyncGenerator) {
            if (!emitAwaitInInnermostScope())
                return false;
        }
    } else {
        /* No explicit return value provided */
        if (!emit1(JSOP_UNDEFINED))
            return false;
    }

    if (needsIteratorResult) {
        if (!emitFinishIteratorResult(true))
            return false;
    }

    // We know functionBodyEndPos is set because "return" is only
    // valid in a function, and so we've passed through
    // emitFunctionScript.
    MOZ_ASSERT(functionBodyEndPosSet);
    if (!updateSourceCoordNotes(functionBodyEndPos))
        return false;

    /*
     * EmitNonLocalJumpFixup may add fixup bytecode to close open try
     * blocks having finally clauses and to exit intermingled let blocks.
     * We can't simply transfer control flow to our caller in that case,
     * because we must gosub to those finally clauses from inner to outer,
     * with the correct stack pointer (i.e., after popping any with,
     * for/in, etc., slots nested inside the finally's try).
     *
     * In this case we mutate JSOP_RETURN into JSOP_SETRVAL and add an
     * extra JSOP_RETRVAL after the fixups.
     */
    ptrdiff_t top = offset();

    bool needsFinalYield = sc->isFunctionBox() && sc->asFunctionBox()->needsFinalYield();
    bool isDerivedClassConstructor =
        sc->isFunctionBox() && sc->asFunctionBox()->isDerivedClassConstructor();

    if (!emit1((needsFinalYield || isDerivedClassConstructor) ? JSOP_SETRVAL : JSOP_RETURN))
        return false;

    // Make sure that we emit this before popping the blocks in prepareForNonLocalJump,
    // to ensure that the error is thrown while the scope-chain is still intact.
    if (isDerivedClassConstructor) {
        if (!emitCheckDerivedClassConstructorReturn())
            return false;
    }

    NonLocalExitControl nle(this, NonLocalExitControl::Return);

    if (!nle.prepareForNonLocalJumpToOutermost())
        return false;

    if (needsFinalYield) {
        // We know that .generator is on the function scope, as we just exited
        // all nested scopes.
        NameLocation loc =
            *locationOfNameBoundInFunctionScope(cx->names().dotGenerator, varEmitterScope);
        if (!emitGetNameAtLocation(cx->names().dotGenerator, loc))
            return false;
        if (!emitYieldOp(JSOP_FINALYIELDRVAL))
            return false;
    } else if (isDerivedClassConstructor) {
        MOZ_ASSERT(code()[top] == JSOP_SETRVAL);
        if (!emit1(JSOP_RETRVAL))
            return false;
    } else if (top + static_cast<ptrdiff_t>(JSOP_RETURN_LENGTH) != offset()) {
        code()[top] = JSOP_SETRVAL;
        if (!emit1(JSOP_RETRVAL))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitGetDotGeneratorInScope(EmitterScope& currentScope)
{
    NameLocation loc = *locationOfNameBoundInFunctionScope(cx->names().dotGenerator, &currentScope);
    return emitGetNameAtLocation(cx->names().dotGenerator, loc);
}

bool
BytecodeEmitter::emitInitialYield(ParseNode* pn)
{
    if (!emitTree(pn->pn_kid))
        return false;

    if (!emitYieldOp(JSOP_INITIALYIELD))
        return false;

    if (!emit1(JSOP_POP))
        return false;

    return true;
}

bool
BytecodeEmitter::emitYield(ParseNode* pn)
{
    MOZ_ASSERT(sc->isFunctionBox());
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Yield));

    bool needsIteratorResult = sc->asFunctionBox()->needsIteratorResult();
    if (needsIteratorResult) {
        if (!emitPrepareIteratorResult())
            return false;
    }
    if (pn->pn_kid) {
        if (!emitTree(pn->pn_kid))
            return false;
    } else {
        if (!emit1(JSOP_UNDEFINED))
            return false;
    }

    // 11.4.3.7 AsyncGeneratorYield step 5.
    bool isAsyncGenerator = sc->asFunctionBox()->isAsync();
    if (isAsyncGenerator) {
        if (!emitAwaitInInnermostScope())                 // RESULT
            return false;
    }

    if (needsIteratorResult) {
        if (!emitFinishIteratorResult(false))
            return false;
    }

    if (!emitGetDotGeneratorInInnermostScope())
        return false;

    if (!emitYieldOp(JSOP_YIELD))
        return false;

    return true;
}

bool
BytecodeEmitter::emitAwaitInInnermostScope(ParseNode* pn)
{
    MOZ_ASSERT(sc->isFunctionBox());
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Await));

    if (!emitTree(pn->pn_kid))
        return false;
    return emitAwaitInInnermostScope();
}

bool
BytecodeEmitter::emitAwaitInScope(EmitterScope& currentScope)
{
    if (!emitGetDotGeneratorInScope(currentScope))
        return false;
    if (!emitYieldOp(JSOP_AWAIT))
        return false;
    return true;
}

bool
BytecodeEmitter::emitYieldStar(ParseNode* iter)
{
    MOZ_ASSERT(sc->isFunctionBox());
    MOZ_ASSERT(sc->asFunctionBox()->isStarGenerator());

    bool isAsyncGenerator = sc->asFunctionBox()->isAsync();

    if (!emitTree(iter))                                  // ITERABLE
        return false;
    if (isAsyncGenerator) {
        if (!emitAsyncIterator())                         // ITER
            return false;
    } else {
        if (!emitIterator())                              // ITER
            return false;
    }

    // Initial send value is undefined.
    if (!emit1(JSOP_UNDEFINED))                           // ITER RECEIVED
        return false;

    int32_t savedDepthTemp;
    int32_t startDepth = stackDepth;
    MOZ_ASSERT(startDepth >= 2);

    TryEmitter tryCatch(this, TryEmitter::Kind::TryCatchFinally,
                        TryEmitter::ControlKind::NonSyntactic);
    if (!tryCatch.emitJumpOverCatchAndFinally())          // ITER RESULT
        return false;

    JumpTarget tryStart{ offset() };
    if (!tryCatch.emitTry())                              // ITER RESULT
        return false;

    MOZ_ASSERT(this->stackDepth == startDepth);

    // 11.4.3.7 AsyncGeneratorYield step 5.
    if (isAsyncGenerator) {
        if (!emitAwaitInInnermostScope())                 // NEXT ITER RESULT
            return false;
    }

    // Load the generator object.
    if (!emitGetDotGeneratorInInnermostScope())           // NEXT ITER RESULT GENOBJ
        return false;

    // Yield RESULT as-is, without re-boxing.
    if (!emitYieldOp(JSOP_YIELD))                         // ITER RECEIVED
        return false;

    if (!tryCatch.emitCatch())                            // ITER RESULT EXCEPTION
        return false;

    // The exception was already pushed by emitCatch().
    MOZ_ASSERT(stackDepth == startDepth + 1);

    if (!emitDupAt(2))                                    // ITER RESULT EXCEPTION ITER
        return false;
    if (!emit1(JSOP_DUP))                                 // ITER RESULT EXCEPTION ITER ITER
        return false;
    if (!emitAtomOp(cx->names().throw_, JSOP_CALLPROP))   // ITER RESULT EXCEPTION ITER THROW
        return false;
    if (!emit1(JSOP_DUP))                                 // ITER RESULT EXCEPTION ITER THROW THROW
        return false;
    if (!emit1(JSOP_UNDEFINED))                           // ITER RESULT EXCEPTION ITER THROW THROW UNDEFINED
        return false;
    if (!emit1(JSOP_EQ))                                  // ITER RESULT EXCEPTION ITER THROW ?EQL
        return false;

    InternalIfEmitter ifThrowMethodIsNotDefined(this);
    if (!ifThrowMethodIsNotDefined.emitThen())            // ITER RESULT EXCEPTION ITER THROW
        return false;
    savedDepthTemp = stackDepth;
    if (!emit1(JSOP_POP))                                 // ITER RESULT EXCEPTION ITER
        return false;
    // ES 14.4.13, YieldExpression : yield * AssignmentExpression, step 5.b.iii.2
    //
    // If the iterator does not have a "throw" method, it calls IteratorClose
    // and then throws a TypeError.
    IteratorKind iterKind = isAsyncGenerator ? IteratorKind::Async : IteratorKind::Sync;
    if (!emitIteratorCloseInInnermostScope(iterKind))     // NEXT ITER RESULT EXCEPTION
        return false;
    if (!emitUint16Operand(JSOP_THROWMSG, JSMSG_ITERATOR_NO_THROW)) // throw
        return false;
    stackDepth = savedDepthTemp;
    if (!ifThrowMethodIsNotDefined.emitEnd())             // ITER OLDRESULT EXCEPTION ITER THROW
        return false;
    // ES 14.4.13, YieldExpression : yield * AssignmentExpression, step 5.b.iii.4.
    // RESULT = ITER.throw(EXCEPTION)                     // ITER OLDRESULT EXCEPTION ITER THROW
    if (!emit1(JSOP_SWAP))                                // ITER OLDRESULT EXCEPTION THROW ITER
        return false;
    if (!emit2(JSOP_PICK, 2))                             // ITER OLDRESULT THROW ITER EXCEPTION
        return false;
    if (!emitCall(JSOP_CALL, 1, iter))                    // ITER OLDRESULT RESULT
        return false;
    checkTypeSet(JSOP_CALL);

    if (isAsyncGenerator) {
        if (!emitAwaitInInnermostScope())                 // NEXT ITER OLDRESULT RESULT
            return false;
    }

    if (!emitCheckIsObj(CheckIsObjectKind::IteratorThrow)) // ITER OLDRESULT RESULT
        return false;
    if (!emit1(JSOP_SWAP))                                // ITER RESULT OLDRESULT
        return false;
    if (!emit1(JSOP_POP))                                 // ITER RESULT
        return false;
    MOZ_ASSERT(this->stackDepth == startDepth);
    JumpList checkResult;
    // ES 14.4.13, YieldExpression : yield * AssignmentExpression, step 5.b.ii.
    //
    // Note that there is no GOSUB to the finally block here. If the iterator has a
    // "throw" method, it does not perform IteratorClose.
    if (!emitJump(JSOP_GOTO, &checkResult))               // goto checkResult
        return false;

    if (!tryCatch.emitFinally())
         return false;

    // ES 14.4.13, yield * AssignmentExpression, step 5.c
    //
    // Call iterator.return() for receiving a "forced return" completion from
    // the generator.

    InternalIfEmitter ifGeneratorClosing(this);
    if (!emit1(JSOP_ISGENCLOSING))                        // ITER RESULT FTYPE FVALUE CLOSING
        return false;
    if (!ifGeneratorClosing.emitThen())                   // ITER RESULT FTYPE FVALUE
        return false;

    // Step ii.
    //
    // Get the "return" method.
    if (!emitDupAt(3))                                    // ITER RESULT FTYPE FVALUE ITER
        return false;
    if (!emit1(JSOP_DUP))                                 // ITER RESULT FTYPE FVALUE ITER ITER
        return false;
    if (!emitAtomOp(cx->names().return_, JSOP_CALLPROP))  // ITER RESULT FTYPE FVALUE ITER RET
        return false;

    // Step iii.
    //
    // Do nothing if "return" is undefined or null.
    InternalIfEmitter ifReturnMethodIsDefined(this);
    if (!emitPushNotUndefinedOrNull())                    // ITER RESULT FTYPE FVALUE ITER RET NOT-UNDEF-OR-NULL
        return false;

    // Step iv.
    //
    // Call "return" with the argument passed to Generator.prototype.return,
    // which is currently in rval.value.
    if (!ifReturnMethodIsDefined.emitThenElse())          // ITER OLDRESULT FTYPE FVALUE ITER RET
        return false;
    if (!emit1(JSOP_SWAP))                                // ITER OLDRESULT FTYPE FVALUE RET ITER
        return false;
    if (!emit1(JSOP_GETRVAL))                             // ITER OLDRESULT FTYPE FVALUE RET ITER RVAL
        return false;
    if (!emitAtomOp(cx->names().value, JSOP_GETPROP))     // ITER OLDRESULT FTYPE FVALUE RET ITER VALUE
        return false;
    if (!emitCall(JSOP_CALL, 1))                          // ITER OLDRESULT FTYPE FVALUE RESULT
        return false;
    checkTypeSet(JSOP_CALL);

    if (iterKind == IteratorKind::Async) {
        if (!emitAwaitInInnermostScope())                 // ... FTYPE FVALUE RESULT
            return false;
    }

    // Step v.
    if (!emitCheckIsObj(CheckIsObjectKind::IteratorReturn)) // ITER OLDRESULT FTYPE FVALUE RESULT
        return false;

    // Steps vi-viii.
    //
    // Check if the returned object from iterator.return() is done. If not,
    // continuing yielding.
    InternalIfEmitter ifReturnDone(this);
    if (!emit1(JSOP_DUP))                                 // ITER OLDRESULT FTYPE FVALUE RESULT RESULT
        return false;
    if (!emitAtomOp(cx->names().done, JSOP_GETPROP))      // ITER OLDRESULT FTYPE FVALUE RESULT DONE
        return false;
    if (!ifReturnDone.emitThenElse())                     // ITER OLDRESULT FTYPE FVALUE RESULT
        return false;
    if (!emitAtomOp(cx->names().value, JSOP_GETPROP))     // ITER OLDRESULT FTYPE FVALUE VALUE
        return false;

    if (!emitPrepareIteratorResult())                     // ITER OLDRESULT FTYPE FVALUE VALUE RESULT
        return false;
    if (!emit1(JSOP_SWAP))                                // ITER OLDRESULT FTYPE FVALUE RESULT VALUE
        return false;
    if (!emitFinishIteratorResult(true))                  // ITER OLDRESULT FTYPE FVALUE RESULT
        return false;
    if (!emit1(JSOP_SETRVAL))                             // ITER OLDRESULT FTYPE FVALUE
        return false;
    savedDepthTemp = this->stackDepth;
    if (!ifReturnDone.emitElse())                         // ITER OLDRESULT FTYPE FVALUE RESULT
        return false;
    if (!emit2(JSOP_UNPICK, 3))                           // ITER RESULT OLDRESULT FTYPE FVALUE
        return false;
    if (!emitPopN(3))                                     // ITER RESULT
        return false;
    {
        // goto tryStart;
        JumpList beq;
        JumpTarget breakTarget{ -1 };
        if (!emitBackwardJump(JSOP_GOTO, tryStart, &beq, &breakTarget)) // ITER RESULT
            return false;
    }
    this->stackDepth = savedDepthTemp;
    if (!ifReturnDone.emitEnd())
        return false;

    if (!ifReturnMethodIsDefined.emitElse())              // ITER RESULT FTYPE FVALUE ITER RET
        return false;
    if (!emitPopN(2))                                     // ITER RESULT FTYPE FVALUE
        return false;
    if (!ifReturnMethodIsDefined.emitEnd())
        return false;

    if (!ifGeneratorClosing.emitEnd())
        return false;

    if (!tryCatch.emitEnd())
        return false;

    // After the try-catch-finally block: send the received value to the iterator.
    // result = iter.next(received)                              // ITER RECEIVED
    if (!emit1(JSOP_SWAP))                                       // RECEIVED ITER
        return false;
    if (!emit1(JSOP_DUP))                                        // RECEIVED ITER ITER
        return false;
    if (!emit1(JSOP_DUP))                                        // RECEIVED ITER ITER ITER
        return false;
    if (!emitAtomOp(cx->names().next, JSOP_CALLPROP))            // RECEIVED ITER ITER NEXT
        return false;
    if (!emit1(JSOP_SWAP))                                       // RECEIVED ITER NEXT ITER
        return false;
    if (!emit2(JSOP_PICK, 3))                                    // ITER NEXT ITER RECEIVED
        return false;
    if (!emitCall(JSOP_CALL, 1, iter))                           // ITER RESULT
        return false;
    checkTypeSet(JSOP_CALL);

    if (isAsyncGenerator) {
        if (!emitAwaitInInnermostScope())                        // NEXT ITER RESULT RESULT
            return false;
    }

    if (!emitCheckIsObj(CheckIsObjectKind::IteratorNext))        // ITER RESULT
        return false;
    MOZ_ASSERT(this->stackDepth == startDepth);

    if (!emitJumpTargetAndPatch(checkResult))                    // checkResult:
        return false;

    // if (!result.done) goto tryStart;                          // ITER RESULT
    if (!emit1(JSOP_DUP))                                        // ITER RESULT RESULT
        return false;
    if (!emitAtomOp(cx->names().done, JSOP_GETPROP))             // ITER RESULT DONE
        return false;
    // if (!DONE) goto tryStart;
    {
        JumpList beq;
        JumpTarget breakTarget{ -1 };
        if (!emitBackwardJump(JSOP_IFEQ, tryStart, &beq, &breakTarget)) // ITER RESULT
            return false;
    }

    // result.value
    if (!emit1(JSOP_SWAP))                                       // RESULT ITER
        return false;
    if (!emit1(JSOP_POP))                                        // RESULT
        return false;
    if (!emitAtomOp(cx->names().value, JSOP_GETPROP))            // VALUE
        return false;

    MOZ_ASSERT(this->stackDepth == startDepth - 1);

    return true;
}

bool
BytecodeEmitter::emitStatementList(ParseNode* pn)
{
    MOZ_ASSERT(pn->isArity(PN_LIST));
    for (ParseNode* pn2 = pn->pn_head; pn2; pn2 = pn2->pn_next) {
        if (!emitTree(pn2))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::emitExpressionStatement(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::ExpressionStatement));

    /*
     * Top-level or called-from-a-native JS_Execute/EvaluateScript,
     * debugger, and eval frames may need the value of the ultimate
     * expression statement as the script's result, despite the fact
     * that it appears useless to the compiler.
     *
     * API users may also set the JSOPTION_NO_SCRIPT_RVAL option when
     * calling JS_Compile* to suppress JSOP_SETRVAL.
     */
    bool wantval = false;
    bool useful = false;
    if (sc->isFunctionBox())
        MOZ_ASSERT(!script->noScriptRval());
    else
        useful = wantval = !script->noScriptRval();

    /* Don't eliminate expressions with side effects. */
    ParseNode* expr = pn->pn_kid;
    if (!useful) {
        if (!checkSideEffects(expr, &useful))
            return false;

        /*
         * Don't eliminate apparently useless expressions if they are labeled
         * expression statements. The startOffset() test catches the case
         * where we are nesting in emitTree for a labeled compound statement.
         */
        if (innermostNestableControl &&
            innermostNestableControl->is<LabelControl>() &&
            innermostNestableControl->as<LabelControl>().startOffset() >= offset())
        {
            useful = true;
        }
    }

    if (useful) {
        MOZ_ASSERT_IF(expr->isKind(ParseNodeKind::Assign), expr->isOp(JSOP_NOP));
        ValueUsage valueUsage = wantval ? ValueUsage::WantValue : ValueUsage::IgnoreValue;
        ExpressionStatementEmitter ese(this, valueUsage);
        if (!ese.prepareForExpr(Some(pn->pn_pos.begin))) {
            return false;
        }
        if (!emitTree(expr, valueUsage)) {
            return false;
        }
        if (!ese.emitEnd()) {
            return false;
        }
    } else if (pn->isDirectivePrologueMember()) {
        // Don't complain about directive prologue members; just don't emit
        // their code.
    } else {
        if (JSAtom* atom = pn->isStringExprStatement()) {
            // Warn if encountering a non-directive prologue member string
            // expression statement, that is inconsistent with the current
            // directive prologue.  That is, a script *not* starting with
            // "use strict" should warn for any "use strict" statements seen
            // later in the script, because such statements are misleading.
            const char* directive = nullptr;
            if (atom == cx->names().useStrict) {
                if (!sc->strictScript)
                    directive = js_useStrict_str;
            } else if (atom == cx->names().useAsm) {
                if (sc->isFunctionBox()) {
                    if (IsAsmJSModule(sc->asFunctionBox()->function()))
                        directive = js_useAsm_str;
                }
            }

            if (directive) {
                if (!reportExtraWarning(expr, JSMSG_CONTRARY_NONDIRECTIVE, directive))
                    return false;
            }
        } else {
            if (!reportExtraWarning(expr, JSMSG_USELESS_EXPR))
                return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitDeleteName(ParseNode* node)
{
    MOZ_ASSERT(node->isKind(ParseNodeKind::DeleteName));
    MOZ_ASSERT(node->isArity(PN_UNARY));

    ParseNode* nameExpr = node->pn_kid;
    MOZ_ASSERT(nameExpr->isKind(ParseNodeKind::Name));

    return emitAtomOp(nameExpr->pn_atom, JSOP_DELNAME);
}

bool
BytecodeEmitter::emitDeleteProperty(ParseNode* node)
{
    MOZ_ASSERT(node->isKind(ParseNodeKind::DeleteProp));
    MOZ_ASSERT(node->isArity(PN_UNARY));

    PropertyAccess* propExpr = &node->pn_kid->as<PropertyAccess>();
    PropOpEmitter poe(this,
                      PropOpEmitter::Kind::Delete,
                      propExpr->as<PropertyAccess>().isSuper()
                      ? PropOpEmitter::ObjKind::Super
                      : PropOpEmitter::ObjKind::Other);
    if (propExpr->isSuper()) {
        // The expression |delete super.foo;| has to evaluate |super.foo|,
        // which could throw if |this| hasn't yet been set by a |super(...)|
        // call or the super-base is not an object, before throwing a
        // ReferenceError for attempting to delete a super-reference.
        UnaryNode* base = &propExpr->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {             // THIS
            return false;
        }
    } else {
        if (!poe.prepareForObj()) {
            return false;
        }
        if (!emitPropLHS(propExpr)) {                         // OBJ
            return false;
        }
    }

    if (!poe.emitDelete(propExpr->key().pn_atom)) {       // [Super]
        //                                                // THIS
        //                                                // [Other]
        //                                                // SUCCEEDED
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitDeleteElement(ParseNode* node)
{
    MOZ_ASSERT(node->isKind(ParseNodeKind::DeleteElem));
    MOZ_ASSERT(node->isArity(PN_UNARY));

    PropertyByValue* elemExpr = &node->pn_kid->as<PropertyByValue>();
    bool isSuper = elemExpr->isSuper();
    ElemOpEmitter eoe(this,
                      ElemOpEmitter::Kind::Delete,
                      isSuper
                      ? ElemOpEmitter::ObjKind::Super
                      : ElemOpEmitter::ObjKind::Other);
    if (isSuper) {
        // The expression |delete super[foo];| has to evaluate |super[foo]|,
        // which could throw if |this| hasn't yet been set by a |super(...)|
        // call, or trigger side-effects when evaluating ToPropertyKey(foo),
        // or also throw when the super-base is not an object, before throwing
        // a ReferenceError for attempting to delete a super-reference.
        if (!eoe.prepareForObj()) {                       //
            return false;
        }

        UnaryNode* base = &elemExpr->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {             // THIS
            return false;
        }
        if (!eoe.prepareForKey()) {                       // THIS
            return false;
        }
        if (!emitTree(&elemExpr->key())) {                // THIS KEY
            return false;
        }
    } else {
        if (!emitElemObjAndKey(elemExpr, false, eoe)) {   // OBJ KEY
            return false;
        }
    }
    if (!eoe.emitDelete()) {                              // [Super]
        //                                                // THIS
        //                                                // [Other]
        //                                                // SUCCEEDED
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitDeleteExpression(ParseNode* node)
{
    MOZ_ASSERT(node->isKind(ParseNodeKind::DeleteExpr));
    MOZ_ASSERT(node->isArity(PN_UNARY));

    ParseNode* expression = node->pn_kid;

    // If useless, just emit JSOP_TRUE; otherwise convert |delete <expr>| to
    // effectively |<expr>, true|.
    bool useful = false;
    if (!checkSideEffects(expression, &useful))
        return false;

    if (useful) {
        if (!emitTree(expression))
            return false;
        if (!emit1(JSOP_POP))
            return false;
    }

    return emit1(JSOP_TRUE);
}

bool BytecodeEmitter::emitDeleteOptionalChain(ParseNode* node) {
    MOZ_ASSERT(node->isKind(ParseNodeKind::DeleteOptionalChain));

    OptionalEmitter oe(this, this->stackDepth, JSOP_TRUE);

    if (!oe.emitOptionalJumpLabel())
        return false;

    ParseNode* kid = node->pn_kid;
    switch (kid->getKind()) {
        case ParseNodeKind::Elem:
        case ParseNodeKind::OptionalElem: {
            auto* elemExpr = &kid->as<PropertyByValueBase>();
            if (!emitDeleteElementInOptChain(elemExpr, oe))
                return false;

            break;
        }
        case ParseNodeKind::Dot:
        case ParseNodeKind::OptionalDot: {
            auto* propExpr = &kid->as<PropertyAccessBase>();
            if (!emitDeletePropertyInOptChain(propExpr, oe))
                return false;
            break;
        }
        default:
            MOZ_ASSERT_UNREACHABLE("Unrecognized optional delete ParseNodeKind");
    }

    if (!oe.emitOptionalJumpTarget())
        return false;

    return true;
}

bool BytecodeEmitter::emitDeletePropertyInOptChain(PropertyAccessBase* propExpr,
                                                           OptionalEmitter& oe) {
    MOZ_ASSERT_IF(propExpr->is<PropertyAccess>(),
                  !propExpr->as<PropertyAccess>().isSuper());
    PropOpEmitter poe(this, PropOpEmitter::Kind::Delete,
                      PropOpEmitter::ObjKind::Other);
  
    if (!poe.prepareForObj()) {
        //                [stack]
        return false;
    }
    if (!emitOptionalTree(&propExpr->expression(), oe)) {
        //                [stack] OBJ
        return false;
    }
    if (propExpr->isKind(ParseNodeKind::OptionalDot)) {
        if (!oe.emitJumpShortCircuit()) {
            //            [stack] # if Jump
            //            [stack] UNDEFINED-OR-NULL
            //            [stack] # otherwise
            //            [stack] OBJ
            return false;
        }
    }

    if (!poe.emitDelete(propExpr->key().pn_atom)) {
        //                [stack] SUCCEEDED
        return false;
    }

    return true;
}

bool BytecodeEmitter::emitDeleteElementInOptChain(PropertyByValueBase* elemExpr,
                                                          OptionalEmitter& oe) {
    MOZ_ASSERT_IF(elemExpr->is<PropertyByValue>(),
                  !elemExpr->as<PropertyByValue>().isSuper());
    ElemOpEmitter eoe(this, ElemOpEmitter::Kind::Delete,
                      ElemOpEmitter::ObjKind::Other);

    if (!eoe.prepareForObj()) {
        //                [stack]
        return false;
    }

    if (!emitOptionalTree(&elemExpr->expression(), oe)) {
        //                [stack] OBJ
        return false;
    }

    if (elemExpr->isKind(ParseNodeKind::OptionalElem)) {
        if (!oe.emitJumpShortCircuit()) {
            //            [stack] # if Jump
            //            [stack] UNDEFINED-OR-NULL
            //            [stack] # otherwise
            //            [stack] OBJ
            return false;
        }
    }

    if (!eoe.prepareForKey()) {
        //                [stack] OBJ
        return false;
    }

    if (!emitTree(&elemExpr->key())) {
        //                [stack] OBJ KEY
        return false;
    }

    if (!eoe.emitDelete()) {
        //                [stack] SUCCEEDED
        return false;
    }

    return true;
}

static const char *
SelfHostedCallFunctionName(JSAtom* name, JSContext* cx)
{
    if (name == cx->names().callFunction)
        return "callFunction";
    if (name == cx->names().callContentFunction)
        return "callContentFunction";
    if (name == cx->names().constructContentFunction)
        return "constructContentFunction";

    MOZ_CRASH("Unknown self-hosted call function name");
}

bool
BytecodeEmitter::emitSelfHostedCallFunction(ParseNode* pn)
{
    // Special-casing of callFunction to emit bytecode that directly
    // invokes the callee with the correct |this| object and arguments.
    // callFunction(fun, thisArg, arg0, arg1) thus becomes:
    // - emit lookup for fun
    // - emit lookup for thisArg
    // - emit lookups for arg0, arg1
    //
    // argc is set to the amount of actually emitted args and the
    // emitting of args below is disabled by setting emitArgs to false.
    ParseNode* pn_callee = pn->pn_left;
    ParseNode* pn_args = pn->pn_right;

    const char* errorName = SelfHostedCallFunctionName(pn_callee->name(), cx);

    if (pn_args->pn_count < 2) {
        reportError(pn, JSMSG_MORE_ARGS_NEEDED, errorName, "2", "s");
        return false;
    }

    JSOp callOp = pn->getOp();
    if (callOp != JSOP_CALL) {
        reportError(pn, JSMSG_NOT_CONSTRUCTOR, errorName);
        return false;
    }

    bool constructing = pn_callee->name() == cx->names().constructContentFunction;
    ParseNode* funNode = pn_args->pn_head;
    if (constructing) {
        callOp = JSOP_NEW;
    } else if (funNode->getKind() == ParseNodeKind::Name &&
               funNode->name() == cx->names().std_Function_apply) {
        callOp = JSOP_FUNAPPLY;
    }

    if (!emitTree(funNode))
        return false;

#ifdef DEBUG
    if (emitterMode == BytecodeEmitter::SelfHosting &&
        pn_callee->name() == cx->names().callFunction)
    {
        if (!emit1(JSOP_DEBUGCHECKSELFHOSTED))
            return false;
    }
#endif

    ParseNode* thisOrNewTarget = funNode->pn_next;
    if (constructing) {
        // Save off the new.target value, but here emit a proper |this| for a
        // constructing call.
        if (!emit1(JSOP_IS_CONSTRUCTING))
            return false;
    } else {
        // It's |this|, emit it.
        if (!emitTree(thisOrNewTarget))
            return false;
    }

    for (ParseNode* argpn = thisOrNewTarget->pn_next; argpn; argpn = argpn->pn_next) {
        if (!emitTree(argpn))
            return false;
    }

    if (constructing) {
        if (!emitTree(thisOrNewTarget))
            return false;
    }

    uint32_t argc = pn_args->pn_count - 2;
    if (!emitCall(callOp, argc))
        return false;

    checkTypeSet(callOp);
    return true;
}

bool
BytecodeEmitter::emitSelfHostedResumeGenerator(ParseNode* pn)
{
    ParseNode* pn_args = pn->pn_right;

    // Syntax: resumeGenerator(gen, value, 'next'|'throw'|'close')
    if (pn_args->pn_count != 3) {
        reportError(pn, JSMSG_MORE_ARGS_NEEDED, "resumeGenerator", "1", "s");
        return false;
    }

    ParseNode* genNode = pn_args->pn_head;
    if (!emitTree(genNode))
        return false;

    ParseNode* valNode = genNode->pn_next;
    if (!emitTree(valNode))
        return false;

    ParseNode* kindNode = valNode->pn_next;
    MOZ_ASSERT(kindNode->isKind(ParseNodeKind::String));
    uint16_t operand = GeneratorObject::getResumeKind(cx, kindNode->pn_atom);
    MOZ_ASSERT(!kindNode->pn_next);

    if (!emitCall(JSOP_RESUME, operand))
        return false;

    return true;
}

bool
BytecodeEmitter::emitSelfHostedForceInterpreter(ParseNode* pn)
{
    if (!emit1(JSOP_FORCEINTERPRETER))
        return false;
    if (!emit1(JSOP_UNDEFINED))
        return false;
    return true;
}

bool
BytecodeEmitter::emitSelfHostedAllowContentIter(ParseNode* pn)
{
    ParseNode* pn_args = pn->pn_right;

    if (pn_args->pn_count != 1) {
        reportError(pn, JSMSG_MORE_ARGS_NEEDED, "allowContentIter", "1", "");
        return false;
    }

    // We're just here as a sentinel. Pass the value through directly.
    return emitTree(pn_args->pn_head);
}

bool
BytecodeEmitter::emitSelfHostedDefineDataProperty(ParseNode* pn)
{
    ParseNode* pn_args = pn->pn_right;

    // Only optimize when 3 arguments are passed.
    MOZ_ASSERT(pn_args->pn_count == 3);

    ParseNode* objNode = pn_args->pn_head;
    if (!emitTree(objNode))
        return false;

    ParseNode* idNode = objNode->pn_next;
    if (!emitTree(idNode))
        return false;

    ParseNode* valNode = idNode->pn_next;
    if (!emitTree(valNode))
        return false;

    // This will leave the object on the stack instead of pushing |undefined|,
    // but that's fine because the self-hosted code doesn't use the return
    // value.
    return emit1(JSOP_INITELEM);
}

bool
BytecodeEmitter::emitSelfHostedHasOwn(ParseNode* pn)
{
    ParseNode* pn_args = pn->pn_right;

    if (pn_args->pn_count != 2) {
        reportError(pn, JSMSG_MORE_ARGS_NEEDED, "hasOwn", "2", "");
        return false;
    }

    ParseNode* idNode = pn_args->pn_head;
    if (!emitTree(idNode))
        return false;

    ParseNode* objNode = idNode->pn_next;
    if (!emitTree(objNode))
        return false;

    return emit1(JSOP_HASOWN);
}

bool
BytecodeEmitter::emitSelfHostedGetPropertySuper(ParseNode* pn)
{
    ParseNode* pn_args = pn->pn_right;

    if (pn_args->pn_count != 3) {
        reportError(pn, JSMSG_MORE_ARGS_NEEDED, "getPropertySuper", "3", "");
        return false;
    }

    ParseNode* objNode = pn_args->pn_head;
    ParseNode* idNode = objNode->pn_next;
    ParseNode* receiverNode = idNode->pn_next;

    if (!emitTree(receiverNode))
        return false;

    if (!emitTree(idNode))
        return false;

    if (!emitTree(objNode))
        return false;

    return emitElemOpBase(JSOP_GETELEM_SUPER);
}

bool
BytecodeEmitter::isRestParameter(ParseNode* pn)
{
    if (!sc->isFunctionBox())
        return false;

    FunctionBox* funbox = sc->asFunctionBox();
    RootedFunction fun(cx, funbox->function());
    if (!funbox->hasRest())
        return false;

    if (!pn->isKind(ParseNodeKind::Name)) {
        if (emitterMode == BytecodeEmitter::SelfHosting && pn->isKind(ParseNodeKind::Call)) {
            ParseNode* pn_callee = pn->pn_left;
            if (pn_callee->getKind() == ParseNodeKind::Name &&
                pn_callee->name() == cx->names().allowContentIter)
            {
                return isRestParameter(pn->pn_right->pn_head);
            }
        }
        return false;
    }

    JSAtom* name = pn->name();
    Maybe<NameLocation> paramLoc = locationOfNameBoundInFunctionScope(name);
    if (paramLoc && lookupName(name) == *paramLoc) {
        FunctionScope::Data* bindings = funbox->functionScopeBindings();
        if (bindings->nonPositionalFormalStart > 0) {
            // |paramName| can be nullptr when the rest destructuring syntax is
            // used: `function f(...[]) {}`.
            JSAtom* paramName = bindings->names[bindings->nonPositionalFormalStart - 1].name();
            return paramName && name == paramName;
        }
    }

    return false;
}

/* A version of emitCalleeAndThis for the optional cases:
 *   * a?.()
 *   * a?.b()
 *   * a?.["b"]()
 *   * (a?.b)()
 *
 * See emitCallOrNew and emitOptionalCall for more context.
 */
bool BytecodeEmitter::emitOptionalCalleeAndThis(ParseNode* callee,
                                                ParseNode* call,
                                                CallOrNewEmitter& cone,
                                                OptionalEmitter& oe) {
    if (!CheckRecursionLimit(cx)) {
        return false;
    }

    switch (ParseNodeKind kind = callee->getKind()) {
        case ParseNodeKind::Name: {
            RootedAtom nameAtom(cx, callee->as<NameNode>().name());
            if (!cone.emitNameCallee(nameAtom)) {
                //          [stack] CALLEE THIS
                return false;
            }
            break;
        }

        case ParseNodeKind::OptionalDot: {
            MOZ_ASSERT(emitterMode != BytecodeEmitter::SelfHosting);
            OptionalPropertyAccess* prop = &callee->as<OptionalPropertyAccess>();
            bool isSuper = false;

            PropOpEmitter& poe = cone.prepareForPropCallee(isSuper);
            if (!emitOptionalDotExpression(prop, poe, isSuper, oe)) {
                //          [stack] CALLEE THIS
                return false;
            }
            break;
        }
        case ParseNodeKind::Dot: {
            MOZ_ASSERT(emitterMode != BytecodeEmitter::SelfHosting);
            PropertyAccess* prop = &callee->as<PropertyAccess>();
            bool isSuper = prop->isSuper();

            PropOpEmitter& poe = cone.prepareForPropCallee(isSuper);
            if (!emitOptionalDotExpression(prop, poe, isSuper, oe)) {
                //          [stack] CALLEE THIS
                return false;
            }
            break;
        }

        case ParseNodeKind::OptionalElem: {
            OptionalPropertyByValue* elem = &callee->as<OptionalPropertyByValue>();
            bool isSuper = false;

            ElemOpEmitter& eoe = cone.prepareForElemCallee(isSuper);
            if (!emitOptionalElemExpression(elem, eoe, isSuper, oe)) {
                //          [stack] CALLEE THIS
                return false;
            }
            break;
        }
        case ParseNodeKind::Elem: {
            PropertyByValue* elem = &callee->as<PropertyByValue>();
            bool isSuper = elem->isSuper();

            ElemOpEmitter& eoe = cone.prepareForElemCallee(isSuper);
            if (!emitOptionalElemExpression(elem, eoe, isSuper, oe)) {
                //          [stack] CALLEE THIS
                return false;
            }
            break;
        }

        case ParseNodeKind::Function:
            if (!cone.prepareForFunctionCallee()) {
                return false;
            }
            if (!emitOptionalTree(callee, oe)) {
                //          [stack] CALLEE
                return false;
            }
            break;

        case ParseNodeKind::OptionalChain: {
            return emitCalleeAndThisForOptionalChain(callee, call,
                                                     cone);
        }

        default:
            MOZ_RELEASE_ASSERT(kind != ParseNodeKind::SuperBase);

            if (!cone.prepareForOtherCallee()) {
                return false;
            }
            if (!emitOptionalTree(callee, oe)) {
                //          [stack] CALLEE
                return false;
            }
            break;
    }

    if (!cone.emitThis()) {
        //                  [stack] CALLEE THIS
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitCalleeAndThis(ParseNode* callee, ParseNode* call, CallOrNewEmitter& cone)
{
    switch (callee->getKind()) {
      case ParseNodeKind::Name:
        if (!cone.emitNameCallee(callee->name())) {       // CALLEE THIS
            return false;
        }
        break;
      case ParseNodeKind::Dot: {
        MOZ_ASSERT(emitterMode != BytecodeEmitter::SelfHosting);
        PropertyAccess* prop = &callee->as<PropertyAccess>();
        bool isSuper = prop->isSuper();

        PropOpEmitter& poe = cone.prepareForPropCallee(isSuper);
        if (!poe.prepareForObj()) {
            return false;
        }
        if (isSuper) {
            UnaryNode* base = &prop->expression().as<UnaryNode>();
            if (!emitGetThisForSuperBase(base)) {        // THIS
                return false;
            }
        } else {
            if (!emitPropLHS(prop)) {                    // OBJ
                return false;
            }
        }
        if (!poe.emitGet(prop->key().pn_atom)) {          // CALLEE THIS?
            return false;
        }

        break;
      }
      case ParseNodeKind::Elem: {
        MOZ_ASSERT(emitterMode != BytecodeEmitter::SelfHosting);
        PropertyByValue* elem = &callee->as<PropertyByValue>();
        bool isSuper = elem->isSuper();

        ElemOpEmitter& eoe = cone.prepareForElemCallee(isSuper);
        if (!emitElemObjAndKey(elem, isSuper, eoe)) {     // [Super]
            //                                            // THIS? THIS KEY
            //                                            // [needsThis,Other]
            //                                            // OBJ? OBJ KEY
            return false;
        }
        if (!eoe.emitGet()) {                             // CALLEE? THIS
            return false;
        }

        break;
      }
      case ParseNodeKind::Function:
        if (!cone.prepareForFunctionCallee()) {
            return false;
        }
        if (!emitTree(callee)) {                          // CALLEE
            return false;
        }
        break;
      case ParseNodeKind::SuperBase:
        MOZ_ASSERT(call->isKind(ParseNodeKind::SuperCall));
        MOZ_ASSERT(parser.isSuperBase(callee));
        if (!cone.emitSuperCallee()) {                    // CALLEE THIS
            return false;
        }
        break;
      case ParseNodeKind::OptionalChain:
        return emitCalleeAndThisForOptionalChain(callee, call, cone);
        break;
      default:
        if (!cone.prepareForOtherCallee()) {
            return false;
        }
        if (!emitTree(callee)) {
            return false;
        }
        break;
    }

    if (!cone.emitThis()) {                               // CALLEE THIS
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitPipeline(ParseNode* pn)
{
    MOZ_ASSERT(pn->isArity(PN_LIST));
    MOZ_ASSERT(pn->pn_count >= 2);

    if (!emitTree(pn->pn_head)) {                         // ARG
        return false;
    }

    ParseNode* callee = pn->pn_head->pn_next;
    CallOrNewEmitter cone(this, JSOP_CALL,
                          CallOrNewEmitter::ArgumentsKind::Other,
                          ValueUsage::WantValue);
    do {
        if (!emitCalleeAndThis(callee, pn, cone)) {     // ARG CALLEE THIS
            return false;
        }
        if (!emit2(JSOP_PICK, 2)) {                       // CALLEE THIS ARG
            return false;
        }
        if (!cone.emitEnd(1, Some(pn->pn_pos.begin))) { // RVAL
            return false;
        }

        cone.reset();

        checkTypeSet(JSOP_CALL);
    } while ((callee = callee->pn_next));

    return true;
}

ParseNode* BytecodeEmitter::getCoordNode(ParseNode* pn,
                                         ParseNode* calleeNode,
                                         ParseNode* argsList) {
    ParseNode* coordNode = pn;
    if (pn->isOp(JSOP_CALL) || pn->isOp(JSOP_SPREADCALL) || pn->isOp(JSOP_FUNCALL) ||
        pn->isOp(JSOP_FUNAPPLY)) {
        // Default to using the location of the `(` itself.
        // obj[expr]() // expression
        //          ^  // column coord
        coordNode = argsList;

        switch (calleeNode->getKind()) {
          case ParseNodeKind::Dot:
            // Use the position of a property access identifier.
            //
            // obj().aprop() // expression
            //       ^       // column coord
            //
            // Note: Because of the constant folding logic in FoldElement,
            // this case also applies for constant string properties.
            //
            // obj()['aprop']() // expression
            //       ^          // column coord
            coordNode = calleeNode->pn_right;
            break;
          case ParseNodeKind::Name:
            // Use the start of callee names.
            coordNode = calleeNode;
            break;
          default:
            break;
        }
    }
    return coordNode;
}

bool
BytecodeEmitter::emitArguments(ListNode* argsList, bool isCall, bool isSpread,
                               CallOrNewEmitter& cone)
{
    uint32_t argc = argsList->pn_count;
    if (argc >= ARGC_LIMIT) {
        reportError(argsList, isCall ? JSMSG_TOO_MANY_FUN_ARGS : JSMSG_TOO_MANY_CON_ARGS);
        return false;
    }
    if (!isSpread) {
        if (!cone.prepareForNonSpreadArguments()) {       // CALLEE THIS
            return false;
        }
        for (ParseNode* arg = argsList->pn_head; arg; arg = arg->pn_next) {
            if (!emitTree(arg)) {
                return false;
            }
        }
    } else {
        if (cone.wantSpreadOperand()) {
            UnaryNode* spreadNode = &argsList->pn_head->as<UnaryNode>();
            if (!emitTree(spreadNode->pn_kid)) {          // CALLEE THIS ARG0
                return false;
            }
        }
        if (!cone.emitSpreadArgumentsTest()) {            // CALLEE THIS
            return false;
        }
        if (!emitArray(argsList->pn_head, argc)) {        // CALLEE THIS ARR
            return false;
        }
    }

    return true;
}

bool BytecodeEmitter::emitOptionalCall(BinaryNode* node, OptionalEmitter& oe,
                                       ValueUsage valueUsage) {
    /*
     * A modified version of emitCallOrNew that handles optional calls.
     *
     * These include the following:
     *    a?.()
     *    a.b?.()
     *    a.["b"]?.()
     *    (a?.b)?.()
     *
     * See CallOrNewEmitter for more context.
     */
    ParseNode* calleeNode = node->pn_left;
    ListNode* argsList = &node->pn_right->as<ListNode>();
    bool isSpread = JOF_OPTYPE(node->getOp()) == JOF_BYTE;
    JSOp op = node->getOp();
    uint32_t argc = argsList->pn_count;

    CallOrNewEmitter cone(
        this, op,
        isSpread && (argc == 1) &&
                isRestParameter(argsList->pn_head->as<UnaryNode>().pn_kid)
            ? CallOrNewEmitter::ArgumentsKind::SingleSpreadRest
            : CallOrNewEmitter::ArgumentsKind::Other,
        valueUsage);

    ParseNode* coordNode = getCoordNode(node, calleeNode, argsList);

    if (!emitOptionalCalleeAndThis(calleeNode, node, cone, oe)) {
        //              [stack] CALLEE THIS
        return false;
    }

    if (node->isKind(ParseNodeKind::OptionalCall)) {
        if (!oe.emitJumpShortCircuitForCall()) {
            //          [stack] CALLEE THIS
            return false;
        }
    }

    if (!emitArguments(argsList, /* isCall = */ true, isSpread, cone)) {
        //              [stack] CALLEE THIS ARGS...
        return false;
    }

    if (!cone.emitEnd(argc, Some(coordNode->pn_pos.begin))) {
        //              [stack] RVAL
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitCallOrNew(ParseNode* pn, ValueUsage valueUsage /* = ValueUsage::WantValue */)
{
    /*
     * Emit callable invocation or operator new (constructor call) code.
     * First, emit code for the left operand to evaluate the callable or
     * constructable object expression.
     *
     * For operator new, we emit JSOP_GETPROP instead of JSOP_CALLPROP, etc.
     * This is necessary to interpose the lambda-initialized method read
     * barrier -- see the code in jsinterp.cpp for JSOP_LAMBDA followed by
     * JSOP_{SET,INIT}PROP.
     *
     * Then (or in a call case that has no explicit reference-base
     * object) we emit JSOP_UNDEFINED to produce the undefined |this|
     * value required for calls (which non-strict mode functions
     * will box into the global object).
     */
    bool isCall = pn->isKind(ParseNodeKind::Call) ||
                  pn->isKind(ParseNodeKind::TaggedTemplate);
    ParseNode* calleeNode = pn->pn_left;
    ListNode* argsList = &pn->pn_right->as<ListNode>();
    bool isSpread = JOF_OPTYPE(pn->getOp()) == JOF_BYTE;

    if (calleeNode->isKind(ParseNodeKind::Name) &&
        emitterMode == BytecodeEmitter::SelfHosting && !isSpread) {
        // Calls to "forceInterpreter", "callFunction",
        // "callContentFunction", or "resumeGenerator" in self-hosted
        // code generate inline bytecode.
        PropertyName* calleeName = calleeNode->as<NameNode>().name();
        if (calleeName == cx->names().callFunction ||
            calleeName == cx->names().callContentFunction ||
            calleeName == cx->names().constructContentFunction) {
            return emitSelfHostedCallFunction(pn);
        }
        if (calleeName == cx->names().resumeGenerator) {
            return emitSelfHostedResumeGenerator(pn);
        }
        if (calleeName == cx->names().forceInterpreter) {
            return emitSelfHostedForceInterpreter(pn);
        }
        if (calleeName == cx->names().allowContentIter) {
            return emitSelfHostedAllowContentIter(pn);
        }
        if (calleeName == cx->names().defineDataPropertyIntrinsic &&
            argsList->pn_count == 3) {
            return emitSelfHostedDefineDataProperty(pn);
        }
        if (calleeName == cx->names().hasOwn) {
            return emitSelfHostedHasOwn(pn);
        }
        if (calleeName == cx->names().getPropertySuper) {
            return emitSelfHostedGetPropertySuper(pn);
        }
        // Fall through
    }

    JSOp op = pn->getOp();
    uint32_t argc = argsList->pn_count;
    CallOrNewEmitter cone(
        this, op,
        isSpread && (argc == 1) &&
                isRestParameter(argsList->pn_head->as<UnaryNode>().pn_kid)
            ? CallOrNewEmitter::ArgumentsKind::SingleSpreadRest
            : CallOrNewEmitter::ArgumentsKind::Other,
        valueUsage);

    if (!emitCalleeAndThis(calleeNode, pn, cone)) {
        //              [stack] CALLEE THIS
        return false;
    }
    if (!emitArguments(argsList, isCall, isSpread, cone)) {
        //              [stack] CALLEE THIS ARGS...
        return false;
    }

    ParseNode* coordNode = getCoordNode(pn, calleeNode, argsList);

    if (!cone.emitEnd(argc, Some(coordNode->pn_pos.begin))) {
        //              [stack] RVAL
        return false;
    }

    return true;
}

// This list must be kept in the same order in several places:
//   - The binary operators in ParseNode.h ,
//   - the binary operators in TokenKind.h
//   - the precedence list in Parser.cpp
static const JSOp ParseNodeKindToJSOp[] = {
    // JSOP_NOP is for pipeline operator which does not emit its own JSOp
    // but has highest precedence in binary operators
    JSOP_NOP,
    JSOP_COALESCE,
    JSOP_OR,
    JSOP_AND,
    JSOP_BITOR,
    JSOP_BITXOR,
    JSOP_BITAND,
    JSOP_STRICTEQ,
    JSOP_EQ,
    JSOP_STRICTNE,
    JSOP_NE,
    JSOP_LT,
    JSOP_LE,
    JSOP_GT,
    JSOP_GE,
    JSOP_INSTANCEOF,
    JSOP_IN,
    JSOP_LSH,
    JSOP_RSH,
    JSOP_URSH,
    JSOP_ADD,
    JSOP_SUB,
    JSOP_MUL,
    JSOP_DIV,
    JSOP_MOD,
    JSOP_POW
};

static inline JSOp BinaryOpParseNodeKindToJSOp(ParseNodeKind pnk) {
  MOZ_ASSERT(pnk >= ParseNodeKind::BinOpFirst);
  MOZ_ASSERT(pnk <= ParseNodeKind::BinOpLast);
  int parseNodeFirst = size_t(ParseNodeKind::BinOpFirst);
#ifdef DEBUG
  int jsopArraySize = ArrayLength(ParseNodeKindToJSOp);
  int parseNodeKindListSize =
      size_t(ParseNodeKind::BinOpLast) - parseNodeFirst + 1;
  MOZ_ASSERT(jsopArraySize == parseNodeKindListSize);
#endif
  return ParseNodeKindToJSOp[size_t(pnk) - parseNodeFirst];
}

bool
BytecodeEmitter::emitRightAssociative(ParseNode* pn)
{
    // ** is the only right-associative operator.
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Pow));
    MOZ_ASSERT(pn->isArity(PN_LIST));

    // Right-associative operator chain.
    for (ParseNode* subexpr = pn->pn_head; subexpr; subexpr = subexpr->pn_next) {
        if (!emitTree(subexpr))
            return false;
    }
    for (uint32_t i = 0; i < pn->pn_count - 1; i++) {
        if (!emit1(JSOP_POW))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::emitLeftAssociative(ParseNode* pn)
{
    MOZ_ASSERT(pn->isArity(PN_LIST));

    // Left-associative operator chain.
    if (!emitTree(pn->pn_head))
        return false;
    JSOp op = BinaryOpParseNodeKindToJSOp(pn->getKind());
    ParseNode* nextExpr = pn->pn_head->pn_next;
    do {
        if (!emitTree(nextExpr))
            return false;
        if (!emit1(op))
            return false;
    } while ((nextExpr = nextExpr->pn_next));
    return true;
}

/*
 * Special `emitTree` for Optional Chaining case.
 * Examples of this are `emitOptionalChain`, `emitDeleteOptionalChain` and
 * `emitCalleeAndThisForOptionalChain`.
 */
bool BytecodeEmitter::emitOptionalTree(ParseNode* pn, OptionalEmitter& oe,
                                       ValueUsage valueUsage /* = ValueUsage::WantValue */) {
    if (!CheckRecursionLimit(cx)) {
        return false;
    }

    ParseNodeKind kind = pn->getKind();
    switch (kind) {
        case ParseNodeKind::OptionalDot: {
            OptionalPropertyAccess* prop = &pn->as<OptionalPropertyAccess>();
            bool isSuper = false;
            PropOpEmitter poe(this, PropOpEmitter::Kind::Get,
                              PropOpEmitter::ObjKind::Other);
            if (!emitOptionalDotExpression(prop, poe, isSuper, oe))
                return false;
            break;
        }
        case ParseNodeKind::Dot: {
            PropertyAccess* prop = &pn->as<PropertyAccess>();
            bool isSuper = prop->isSuper();
            PropOpEmitter poe(this, PropOpEmitter::Kind::Get,
                              isSuper ? PropOpEmitter::ObjKind::Super
                                      : PropOpEmitter::ObjKind::Other);
            if (!emitOptionalDotExpression(prop, poe, isSuper, oe))
                return false;
            break;
        }

        case ParseNodeKind::OptionalElem: {
            OptionalPropertyByValue* elem = &pn->as<OptionalPropertyByValue>();
            bool isSuper = false;
            ElemOpEmitter eoe(this, ElemOpEmitter::Kind::Get,
                              ElemOpEmitter::ObjKind::Other);

            if (!emitOptionalElemExpression(elem, eoe, isSuper, oe))
                return false;
            break;
        }
        case ParseNodeKind::Elem: {
            PropertyByValue* elem = &pn->as<PropertyByValue>();
            bool isSuper = elem->isSuper();
            ElemOpEmitter eoe(this, ElemOpEmitter::Kind::Get,
                              isSuper ? ElemOpEmitter::ObjKind::Super
                                      : ElemOpEmitter::ObjKind::Other);

            if (!emitOptionalElemExpression(elem, eoe, isSuper, oe))
                return false;
            break;
        }

        case ParseNodeKind::Call:
        case ParseNodeKind::OptionalCall:
            if (!emitOptionalCall(&pn->as<BinaryNode>(), oe, valueUsage))
                return false;
            break;

        // List of accepted ParseNodeKinds that might appear only at the beginning
        // of an Optional Chain.
        // For example, a taggedTemplateExpr node might occur if we have
        // `test`?.b, with `test` as the taggedTemplateExpr ParseNode.
        default:
#ifdef DEBUG
            // https://tc39.es/ecma262/#sec-primary-expression
            bool isPrimaryExpression =
                kind == ParseNodeKind::This || kind == ParseNodeKind::Name ||
                kind == ParseNodeKind::Null || kind == ParseNodeKind::True ||
                kind == ParseNodeKind::False ||
                kind == ParseNodeKind::Number ||
                /*kind == ParseNodeKind::BigInt || no BigInt-support in Waterfox right now */
                kind == ParseNodeKind::String ||
                kind == ParseNodeKind::Array ||
                kind == ParseNodeKind::Object ||
                kind == ParseNodeKind::Function || kind == ParseNodeKind::Class ||
                kind == ParseNodeKind::RegExp ||
                kind == ParseNodeKind::TemplateString ||
                kind == ParseNodeKind::RawUndefined || pn->isInParens();

            // https://tc39.es/ecma262/#sec-left-hand-side-expressions
            bool isMemberExpression = isPrimaryExpression ||
                                      kind == ParseNodeKind::TaggedTemplate ||
                                      kind == ParseNodeKind::New ||
                                      kind == ParseNodeKind::NewTarget ||
                                      kind == ParseNodeKind::ImportMeta;

            bool isCallExpression = kind == ParseNodeKind::SetThis ||
                                    kind == ParseNodeKind::CallImport;

            MOZ_ASSERT(isMemberExpression || isCallExpression,
                       "Unknown ParseNodeKind for OptionalChain");
#endif
            return emitTree(pn);
    }
    return true;
}

// Handle the case of a call made on a OptionalChainParseNode.
// For example `(a?.b)()` and `(a?.b)?.()`.
bool BytecodeEmitter::emitCalleeAndThisForOptionalChain(ParseNode* optionalChain,
                                                        ParseNode* callNode,
                                                        CallOrNewEmitter& cone) {
    ParseNode* calleeNode = optionalChain->pn_kid;

    // Create a new OptionalEmitter, in order to emit the right bytecode
    // in isolation.
    OptionalEmitter oe(this, this->stackDepth, JSOP_UNDEFINED, OptionalEmitter::Kind::Reference);

    if (!oe.emitOptionalJumpLabel())
        return false;

    if (!emitOptionalCalleeAndThis(calleeNode, callNode, cone, oe))
        return false;

    // complete the jump if necessary. This will set both the "this" value
    // and the "callee" value to undefined, if the callee is undefined. It
    // does not matter much what the this value is, the function call will
    // fail if it is not optional, and be set to undefined otherwise.
    if (!oe.emitOptionalJumpTarget())
        return false;

    return true;
}

bool BytecodeEmitter::emitOptionalChain(ParseNode* node, ValueUsage valueUsage) {
    ParseNode* expr = node->pn_kid;

    OptionalEmitter oe(this, this->stackDepth, JSOP_UNDEFINED);

    if (!oe.emitOptionalJumpLabel())
        return false;

    if (!emitOptionalTree(expr, oe, valueUsage))
        return false;

    if (!oe.emitOptionalJumpTarget())
        return false;

    return true;
}

bool BytecodeEmitter::emitOptionalDotExpression(PropertyAccessBase* prop,
                                                PropOpEmitter& poe, bool isSuper,
                                                OptionalEmitter& oe) {
    if (!poe.prepareForObj()) {
        //              [stack]
        return false;
    }

    if (isSuper) {
        UnaryNode* base = &prop->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {
            //            [stack] OBJ
            return false;
        }
    } else {
        if (!emitOptionalTree(&prop->expression(), oe)) {
            //            [stack] OBJ
            return false;
        }
    }

    if (prop->isKind(ParseNodeKind::OptionalDot)) {
        MOZ_ASSERT(!isSuper);
        if (!oe.emitJumpShortCircuit()) {
            //            [stack] # if Jump
            //            [stack] UNDEFINED-OR-NULL
            //            [stack] # otherwise
            //            [stack] OBJ
            return false;
        }
    }

    if (!poe.emitGet(prop->key().pn_atom)) {
        //              [stack] PROP
        return false;
    }

    return true;
}

bool BytecodeEmitter::emitOptionalElemExpression(PropertyByValueBase* elem,
                                                 ElemOpEmitter& eoe,
                                                 bool isSuper,
                                                 OptionalEmitter& oe) {
    if (!eoe.prepareForObj()) {
        //              [stack]
        return false;
    }

    if (isSuper) {
        UnaryNode* base = &elem->expression().as<UnaryNode>();
        if (!emitGetThisForSuperBase(base)) {
            //            [stack] OBJ
            return false;
        }
    } else {
        if (!emitOptionalTree(&elem->expression(), oe)) {
            //            [stack] OBJ
            return false;
        }
    }

    if (elem->isKind(ParseNodeKind::OptionalElem)) {
        MOZ_ASSERT(!isSuper);
        if (!oe.emitJumpShortCircuit()) {
            //            [stack] # if Jump
            //            [stack] UNDEFINED-OR-NULL
            //            [stack] # otherwise
            //            [stack] OBJ
            return false;
        }
    }

    if (!eoe.prepareForKey()) {
        //              [stack] OBJ? OBJ
        return false;
    }

    if (!emitTree(&elem->key())) {
        //              [stack] OBJ? OBJ KEY
        return false;
    }

    if (!eoe.emitGet()) {
        //              [stack] ELEM
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitShortCircuit(ParseNode* pn)
{
    MOZ_ASSERT(pn->isArity(PN_LIST));
    MOZ_ASSERT(pn->isKind(ParseNodeKind::Or) ||
               pn->isKind(ParseNodeKind::CoalesceExpr) ||
               pn->isKind(ParseNodeKind::And));

    /*
     * JSOP_OR converts the operand on the stack to boolean, leaves the original
     * value on the stack and jumps if true; otherwise it falls into the next
     * bytecode, which pops the left operand and then evaluates the right operand.
     * The jump goes around the right operand evaluation.
     *
     * JSOP_AND converts the operand on the stack to boolean and jumps if false;
     * otherwise it falls into the right operand's bytecode.
     */

    TDZCheckCache tdzCache(this);

    /* Left-associative operator chain: avoid too much recursion. */
    ParseNode* pn2 = pn->pn_head;

    if (!emitTree(pn2))
        return false;

    JSOp op;
    switch (pn->getKind()) {
      case ParseNodeKind::Or:
        op = JSOP_OR;
        break;
      case ParseNodeKind::CoalesceExpr:
        op = JSOP_COALESCE;
        break;
      case ParseNodeKind::And:
        op = JSOP_AND;
        break;
      default:
        MOZ_CRASH("Unexpected ParseNodeKind");
    }

    JumpList jump;
    if (!emitJump(op, &jump))
        return false;
    if (!emit1(JSOP_POP))
        return false;

    /* Emit nodes between the head and the tail. */
    while ((pn2 = pn2->pn_next)->pn_next) {
        if (!emitTree(pn2))
            return false;
        if (!emitJump(op, &jump))
            return false;
        if (!emit1(JSOP_POP))
            return false;
    }
    if (!emitTree(pn2))
        return false;

    if (!emitJumpTargetAndPatch(jump))
        return false;
    return true;
}

bool
BytecodeEmitter::emitSequenceExpr(ParseNode* pn,
                                  ValueUsage valueUsage /* = ValueUsage::WantValue */)
{
    for (ParseNode* child = pn->pn_head; ; child = child->pn_next) {
        if (!updateSourceCoordNotes(child->pn_pos.begin))
            return false;
        if (!emitTree(child, child->pn_next ? ValueUsage::IgnoreValue : valueUsage))
            return false;
        if (!child->pn_next)
            break;
        if (!emit1(JSOP_POP))
            return false;
    }
    return true;
}

// Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047. See
// the comment on emitSwitch.
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitIncOrDec(ParseNode* pn)
{
    switch (pn->pn_kid->getKind()) {
      case ParseNodeKind::Dot:
        return emitPropIncDec(pn);
      case ParseNodeKind::Elem:
        return emitElemIncDec(pn);
      case ParseNodeKind::Call:
        return emitCallIncDec(pn);
      default:
        return emitNameIncDec(pn);
    }

    return true;
}

// Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047. See
// the comment on emitSwitch.
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitLabeledStatement(const LabeledStatement* labeledStmt)
{
    LabelEmitter label(this);
    if (!label.emitLabel(labeledStmt->label())) {
        return false;
    }
    if (!emitTree(labeledStmt->statement())) {
        return false;
    }
    if (!label.emitEnd()) {
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitConditionalExpression(ConditionalExpression& conditional,
                                           ValueUsage valueUsage /* = ValueUsage::WantValue */)
{
    /* Emit the condition, then branch if false to the else part. */
    if (!emitTree(&conditional.condition()))
        return false;

    IfEmitter ifThenElse(this);
    if (!ifThenElse.emitCond())
        return false;

    if (!emitTree(&conditional.thenExpression(), valueUsage))
        return false;

    if (!ifThenElse.emitElse())
        return false;

    if (!emitTree(&conditional.elseExpression(), valueUsage))
        return false;

    if (!ifThenElse.emitEnd())
        return false;
    MOZ_ASSERT(ifThenElse.pushed() == 1);

    return true;
}

bool
BytecodeEmitter::emitPropertyList(ParseNode* pn, PropertyEmitter& pe, PropListType type)
{
    //                [stack] CTOR? OBJ

    for (ParseNode* propdef = pn->pn_head; propdef; propdef = propdef->pn_next) {
        // Handle __proto__: v specially because *only* this form, and no other
        // involving "__proto__", performs [[Prototype]] mutation.
        if (propdef->isKind(ParseNodeKind::MutateProto)) {
            //            [stack] OBJ
            MOZ_ASSERT(type == ObjectLiteral);
            if (!pe.prepareForProtoValue(Some(propdef->pn_pos.begin))) {
                //          [stack] OBJ
                return false;
            }
            if (!emitTree(propdef->pn_kid)) {
                //          [stack] OBJ PROTO
                return false;
            }
            if (!pe.emitMutateProto()) {
                //          [stack] OBJ
                return false;
            }
            continue;
        }

        if (propdef->isKind(ParseNodeKind::Spread)) {
            MOZ_ASSERT(type == ObjectLiteral);
            //            [stack] OBJ
            if (!pe.prepareForSpreadOperand(Some(propdef->pn_pos.begin))) {
                //          [stack] OBJ OBJ
                return false;
            }
            if (!emitTree(propdef->pn_kid)) {
                //          [stack] OBJ OBJ VAL
                return false;
            }
            if (!pe.emitSpread()) {
                //          [stack] OBJ
                return false;
            }
            continue;
        }

        BinaryNode* prop = &propdef->as<BinaryNode>();

        ParseNode* key = prop->pn_left;
        ParseNode* propVal = prop->pn_right;
        JSOp op = propdef->getOp();
        MOZ_ASSERT(op == JSOP_INITPROP || op == JSOP_INITPROP_GETTER ||
                   op == JSOP_INITPROP_SETTER);

        auto emitValue = [this, &key, &propVal, op, &pe]() {
            //            [stack] CTOR? OBJ CTOR? KEY?

            if (propVal->isDirectRHSAnonFunction()) {
                if (key->isKind(ParseNodeKind::Number)) {
                  MOZ_ASSERT(op == JSOP_INITPROP);

                  RootedAtom keyAtom(cx, NumberToAtom(cx, key->pn_dval));
                  if (!keyAtom) {
                      return false;
                  }
                  if (!emitAnonymousFunctionWithName(propVal, keyAtom)) {
                      //      [stack] CTOR? OBJ CTOR? KEY VAL
                      return false;
                  }
              } else if (key->isKind(ParseNodeKind::ObjectPropertyName) ||
                         key->isKind(ParseNodeKind::String)) {
                  MOZ_ASSERT(op == JSOP_INITPROP);

                  RootedAtom keyAtom(cx, key->pn_atom);
                  if (!emitAnonymousFunctionWithName(propVal, keyAtom)) {
                      //      [stack] CTOR? OBJ CTOR? VAL
                      return false;
                  }
              } else {
                  MOZ_ASSERT(key->isKind(ParseNodeKind::ComputedName));

                  FunctionPrefixKind prefix = op == JSOP_INITPROP
                                                  ? FunctionPrefixKind::None
                                                  : op == JSOP_INITPROP_GETTER
                                                        ? FunctionPrefixKind::Get
                                                        : FunctionPrefixKind::Set;

                  if (!emitAnonymousFunctionWithComputedName(propVal, prefix)) {
                      //      [stack] CTOR? OBJ CTOR? KEY VAL
                      return false;
                  }
              }
            } else {
              if (!emitTree(propVal)) {
                //        [stack] CTOR? OBJ CTOR? KEY? VAL
                return false;
              }
            }

            if (propVal->isKind(ParseNodeKind::Function) &&
                propVal->pn_funbox->needsHomeObject()) {
                FunctionBox* funbox = propVal->pn_funbox;
                MOZ_ASSERT(funbox->function()->allowSuperProperty());

                if (!pe.emitInitHomeObject(funbox->asyncKind())) {
                    //        [stack] CTOR? OBJ CTOR? KEY? FUN
                    return false;
                }
            }
          return true;
        };

        PropertyEmitter::Kind kind =
            (type == ClassBody && propdef->as<ClassMethod>().isStatic())
                ? PropertyEmitter::Kind::Static
                : PropertyEmitter::Kind::Prototype;
        if (key->isKind(ParseNodeKind::Number)) {
            //            [stack] CTOR? OBJ
            if (!pe.prepareForIndexPropKey(Some(propdef->pn_pos.begin), kind)) {
              //          [stack] CTOR? OBJ CTOR?
              return false;
            }
            if (!emitNumberOp(key->pn_dval)) {
                //          [stack] CTOR? OBJ CTOR? KEY
                return false;
            }
            if (!pe.prepareForIndexPropValue()) {
                //          [stack] CTOR? OBJ CTOR? KEY
                return false;
            }
            if (!emitValue()) {
                //          [stack] CTOR? OBJ CTOR? KEY VAL
                return false;
            }

            switch (op) {
              case JSOP_INITPROP:
                if (!pe.emitInitIndexProp()) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              case JSOP_INITPROP_GETTER:
                if (!pe.emitInitIndexGetter()) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              case JSOP_INITPROP_SETTER:
                if (!pe.emitInitIndexSetter()) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              default:
                MOZ_CRASH("Invalid op");
            }

            continue;
        }

        if (key->isKind(ParseNodeKind::ObjectPropertyName) ||
            key->isKind(ParseNodeKind::String)) {
            //            [stack] CTOR? OBJ

            // emitClass took care of constructor already.
            if (type == ClassBody && key->pn_atom == cx->names().constructor &&
              !propdef->as<ClassMethod>().isStatic()) {
                continue;
            }

            if (!pe.prepareForPropValue(Some(propdef->pn_pos.begin), kind)) {
                //          [stack] CTOR? OBJ CTOR?
                return false;
            }
            if (!emitValue()) {
                //          [stack] CTOR? OBJ CTOR? VAL
                return false;
            }

            RootedAtom keyAtom(cx, key->pn_atom);
            switch (op) {
              case JSOP_INITPROP:
                if (!pe.emitInitProp(keyAtom)) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              case JSOP_INITPROP_GETTER:
                if (!pe.emitInitGetter(keyAtom)) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              case JSOP_INITPROP_SETTER:
                if (!pe.emitInitSetter(keyAtom)) {
                    //      [stack] CTOR? OBJ
                    return false;
                }
                break;
              default: MOZ_CRASH("Invalid op");
            }

            continue;
        }

        MOZ_ASSERT(key->isKind(ParseNodeKind::ComputedName));

        //              [stack] CTOR? OBJ

        if (!pe.prepareForComputedPropKey(Some(propdef->pn_pos.begin), kind)) {
            //            [stack] CTOR? OBJ CTOR?
            return false;
        }
        if (!emitTree(key->pn_kid)) {
            //            [stack] CTOR? OBJ CTOR? KEY
            return false;
        }
        if (!pe.prepareForComputedPropValue()) {
            //            [stack] CTOR? OBJ CTOR? KEY
            return false;
        }
        if (!emitValue()) {
            //            [stack] CTOR? OBJ CTOR? KEY VAL
            return false;
        }

        switch (op) {
        case JSOP_INITPROP:
          if (!pe.emitInitComputedProp()) {
              //        [stack] CTOR? OBJ
              return false;
          }
          break;
        case JSOP_INITPROP_GETTER:
          if (!pe.emitInitComputedGetter()) {
              //        [stack] CTOR? OBJ
              return false;
          }
          break;
        case JSOP_INITPROP_SETTER:
          if (!pe.emitInitComputedSetter()) {
              //        [stack] CTOR? OBJ
              return false;
          }
          break;
        default:
          MOZ_CRASH("Invalid op");
        }
  }
  return true;
}

// Using MOZ_NEVER_INLINE in here is a workaround for llvm.org/pr14047. See
// the comment on emitSwitch.
MOZ_NEVER_INLINE bool
BytecodeEmitter::emitObject(ParseNode* pn)
{
    if (!(pn->pn_xflags & PNX_NONCONST) && pn->pn_head && checkSingletonContext()) {
        return emitSingletonInitialiser(pn);
    }

    //                [stack]

    ObjectEmitter oe(this);
    if (!oe.emitObject(pn->pn_count)) {
        //              [stack] OBJ
        return false;
    }
    if (!emitPropertyList(pn, oe, ObjectLiteral)) {
        //              [stack] OBJ
        return false;
    }
    if (!oe.emitEnd()) {
        //              [stack] OBJ
        return false;
    }

    return true;
}

bool
BytecodeEmitter::replaceNewInitWithNewObject(JSObject* obj, ptrdiff_t offset)
{
    ObjectBox* objbox = parser.newObjectBox(obj);
    if (!objbox)
        return false;

    static_assert(JSOP_NEWINIT_LENGTH == JSOP_NEWOBJECT_LENGTH,
                  "newinit and newobject must have equal length to edit in-place");

    uint32_t index = objectList.add(objbox);
    jsbytecode* code = this->code(offset);

    MOZ_ASSERT(code[0] == JSOP_NEWINIT);
    code[0] = JSOP_NEWOBJECT;
    SET_UINT32(code, index);

    return true;
}

bool
BytecodeEmitter::emitArrayComp(ParseNode* pn)
{
    if (!emitNewInit(JSProto_Array))
        return false;

    /*
     * Pass the new array's stack index to theParseNodeKind::ArrayPush case via
     * arrayCompDepth, then simply traverse theParseNodeKind::For node and
     * its kids under pn2 to generate this comprehension.
     */
    MOZ_ASSERT(stackDepth > 0);
    uint32_t saveDepth = arrayCompDepth;
    arrayCompDepth = (uint32_t) (stackDepth - 1);
    if (!emitTree(pn->pn_head))
        return false;
    arrayCompDepth = saveDepth;

    return true;
}

bool
BytecodeEmitter::emitArrayLiteral(ParseNode* pn)
{
    if (!(pn->pn_xflags & PNX_NONCONST) && pn->pn_head) {
        if (checkSingletonContext()) {
            // Bake in the object entirely if it will only be created once.
            return emitSingletonInitialiser(pn);
        }

        // If the array consists entirely of primitive values, make a
        // template object with copy on write elements that can be reused
        // every time the initializer executes.
        if (emitterMode != BytecodeEmitter::SelfHosting && pn->pn_count != 0) {
            RootedValue value(cx);
            if (!pn->getConstantValue(cx, ParseNode::ForCopyOnWriteArray, &value))
                return false;
            if (!value.isMagic(JS_GENERIC_MAGIC)) {
                // Note: the group of the template object might not yet reflect
                // that the object has copy on write elements. When the
                // interpreter or JIT compiler fetches the template, it should
                // use ObjectGroup::getOrFixupCopyOnWriteObject to make sure the
                // group for the template is accurate. We don't do this here as we
                // want to use ObjectGroup::allocationSiteGroup, which requires a
                // finished script.
                JSObject* obj = &value.toObject();
                MOZ_ASSERT(obj->is<ArrayObject>() &&
                           obj->as<ArrayObject>().denseElementsAreCopyOnWrite());

                ObjectBox* objbox = parser.newObjectBox(obj);
                if (!objbox)
                    return false;

                return emitObjectOp(objbox, JSOP_NEWARRAY_COPYONWRITE);
            }
        }
    }

    return emitArray(pn->pn_head, pn->pn_count);
}

bool
BytecodeEmitter::emitArray(ParseNode* pn, uint32_t count)
{

    /*
     * Emit code for [a, b, c] that is equivalent to constructing a new
     * array and in source order evaluating each element value and adding
     * it to the array, without invoking latent setters.  We use the
     * JSOP_NEWINIT and JSOP_INITELEM_ARRAY bytecodes to ignore setters and
     * to avoid dup'ing and popping the array as each element is added, as
     * JSOP_SETELEM/JSOP_SETPROP would do.
     */

    uint32_t nspread = 0;
    for (ParseNode* elt = pn; elt; elt = elt->pn_next) {
        if (elt->isKind(ParseNodeKind::Spread))
            nspread++;
    }

    // Array literal's length is limited to NELEMENTS_LIMIT in parser.
    static_assert(NativeObject::MAX_DENSE_ELEMENTS_COUNT <= INT32_MAX,
                  "array literals' maximum length must not exceed limits "
                  "required by BaselineCompiler::emit_JSOP_NEWARRAY, "
                  "BaselineCompiler::emit_JSOP_INITELEM_ARRAY, "
                  "and DoSetElemFallback's handling of JSOP_INITELEM_ARRAY");
    MOZ_ASSERT(count >= nspread);
    MOZ_ASSERT(count <= NativeObject::MAX_DENSE_ELEMENTS_COUNT,
               "the parser must throw an error if the array exceeds maximum "
               "length");

    // For arrays with spread, this is a very pessimistic allocation, the
    // minimum possible final size.
    if (!emitUint32Operand(JSOP_NEWARRAY, count - nspread))         // ARRAY
        return false;

    ParseNode* pn2 = pn;
    uint32_t index;
    bool afterSpread = false;
    for (index = 0; pn2; index++, pn2 = pn2->pn_next) {
        if (!afterSpread && pn2->isKind(ParseNodeKind::Spread)) {
            afterSpread = true;
            if (!emitNumberOp(index))                               // ARRAY INDEX
                return false;
        }
        if (!updateSourceCoordNotes(pn2->pn_pos.begin))
            return false;

        bool allowSelfHostedIter = false;
        if (pn2->isKind(ParseNodeKind::Elision)) {
            if (!emit1(JSOP_HOLE))
                return false;
        } else {
            ParseNode* expr;
            if (pn2->isKind(ParseNodeKind::Spread)) {
                expr = pn2->pn_kid;

                if (emitterMode == BytecodeEmitter::SelfHosting &&
                    expr->isKind(ParseNodeKind::Call) &&
                    expr->pn_left->name() == cx->names().allowContentIter)
                {
                    allowSelfHostedIter = true;
                }
            } else {
                expr = pn2;
            }
            if (!emitTree(expr))                                         // ARRAY INDEX? VALUE
                return false;
        }
        if (pn2->isKind(ParseNodeKind::Spread)) {
            if (!emitIterator())                                         // ARRAY INDEX ITER
                return false;
            if (!emit2(JSOP_PICK, 2))                                    // INDEX ITER ARRAY
                return false;
            if (!emit2(JSOP_PICK, 2))                                    // ITER ARRAY INDEX
                return false;
            if (!emitSpread(allowSelfHostedIter))                        // ARRAY INDEX
                return false;
        } else if (afterSpread) {
            if (!emit1(JSOP_INITELEM_INC))
                return false;
        } else {
            if (!emitUint32Operand(JSOP_INITELEM_ARRAY, index))
                return false;
        }
    }
    MOZ_ASSERT(index == count);
    if (afterSpread) {
        if (!emit1(JSOP_POP))                                            // ARRAY
            return false;
    }
    return true;
}

static inline JSOp
UnaryOpParseNodeKindToJSOp(ParseNodeKind pnk)
{
    switch (pnk) {
      case ParseNodeKind::Throw: return JSOP_THROW;
      case ParseNodeKind::Void: return JSOP_VOID;
      case ParseNodeKind::Not: return JSOP_NOT;
      case ParseNodeKind::BitNot: return JSOP_BITNOT;
      case ParseNodeKind::Pos: return JSOP_POS;
      case ParseNodeKind::Neg: return JSOP_NEG;
      default: MOZ_CRASH("unexpected unary op");
    }
}

bool
BytecodeEmitter::emitUnary(ParseNode* pn)
{
    if (!updateSourceCoordNotes(pn->pn_pos.begin))
        return false;
    if (!emitTree(pn->pn_kid))
        return false;
    return emit1(UnaryOpParseNodeKindToJSOp(pn->getKind()));
}

bool
BytecodeEmitter::emitTypeof(ParseNode* node, JSOp op)
{
    MOZ_ASSERT(op == JSOP_TYPEOF || op == JSOP_TYPEOFEXPR);

    if (!updateSourceCoordNotes(node->pn_pos.begin))
        return false;

    if (!emitTree(node->pn_kid))
        return false;

    return emit1(op);
}

bool
BytecodeEmitter::emitFunctionFormalParametersAndBody(ParseNode *pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::ParamsBody));

    ParseNode* funBody = pn->last();
    FunctionBox* funbox = sc->asFunctionBox();

    TDZCheckCache tdzCache(this);

    if (funbox->hasParameterExprs) {
        EmitterScope funEmitterScope(this);
        if (!funEmitterScope.enterFunction(this, funbox))
            return false;

        if (!emitInitializeFunctionSpecialNames())
            return false;

        if (!emitFunctionFormalParameters(pn))
            return false;

        {
            Maybe<EmitterScope> extraVarEmitterScope;

            if (funbox->hasExtraBodyVarScope()) {
                extraVarEmitterScope.emplace(this);
                if (!extraVarEmitterScope->enterFunctionExtraBodyVar(this, funbox))
                    return false;

                // After emitting expressions for all parameters, copy over any
                // formal parameters which have been redeclared as vars. For
                // example, in the following, the var y in the body scope is 42:
                //
                //   function f(x, y = 42) { var y; }
                //
                RootedAtom name(cx);
                if (funbox->extraVarScopeBindings() && funbox->functionScopeBindings()) {
                    for (BindingIter bi(*funbox->functionScopeBindings(), true); bi; bi++) {
                        name = bi.name();

                        // There may not be a var binding of the same name.
                        if (!locationOfNameBoundInScope(name, extraVarEmitterScope.ptr()))
                            continue;

                        // The '.this' and '.generator' function special
                        // bindings should never appear in the extra var
                        // scope. 'arguments', however, may.
                        MOZ_ASSERT(name != cx->names().dotThis &&
                                   name != cx->names().dotGenerator);

                        NameOpEmitter noe(this, name, NameOpEmitter::Kind::Initialize);
                        if (!noe.prepareForRhs()) {
                            return false;
                        }

                        NameLocation paramLoc = *locationOfNameBoundInScope(name, &funEmitterScope);
                        if (!emitGetNameAtLocation(name, paramLoc)) {
                            return false;
                        }
                        if (!noe.emitAssignment()) {
                            return false;
                        }
                        if (!emit1(JSOP_POP)) {
                            return false;
                        }
                    }
                }
            }

            if (!emitFunctionBody(funBody))
                return false;

            if (extraVarEmitterScope && !extraVarEmitterScope->leave(this))
                return false;
        }

        return funEmitterScope.leave(this);
    }

    // No parameter expressions. Enter the function body scope and emit
    // everything.
    //
    // One caveat is that Debugger considers ops in the prologue to be
    // unreachable (i.e. cannot set a breakpoint on it). If there are no
    // parameter exprs, any unobservable environment ops (like pushing the
    // call object, setting '.this', etc) need to go in the prologue, else it
    // messes up breakpoint tests.
    EmitterScope emitterScope(this);

    switchToPrologue();
    if (!emitterScope.enterFunction(this, funbox))
        return false;

    if (!emitInitializeFunctionSpecialNames())
        return false;
    switchToMain();

    if (!emitFunctionFormalParameters(pn))
        return false;

    if (!emitFunctionBody(funBody))
        return false;

    return emitterScope.leave(this);
}

bool
BytecodeEmitter::emitFunctionFormalParameters(ParseNode* pn)
{
    ParseNode* funBody = pn->last();
    FunctionBox* funbox = sc->asFunctionBox();
    EmitterScope* funScope = innermostEmitterScope();

    bool hasParameterExprs = funbox->hasParameterExprs;
    bool hasRest = funbox->hasRest();

    uint16_t argSlot = 0;
    for (ParseNode* arg = pn->pn_head; arg != funBody; arg = arg->pn_next, argSlot++) {
        ParseNode* bindingElement = arg;
        ParseNode* initializer = nullptr;
        if (arg->isKind(ParseNodeKind::Assign)) {
            bindingElement = arg->pn_left;
            initializer = arg->pn_right;
        }

        // Left-hand sides are either simple names or destructuring patterns.
        MOZ_ASSERT(bindingElement->isKind(ParseNodeKind::Name) ||
                   bindingElement->isKind(ParseNodeKind::Array) ||
                   bindingElement->isKind(ParseNodeKind::ArrayComp) ||
                   bindingElement->isKind(ParseNodeKind::Object));

        // The rest parameter doesn't have an initializer.
        bool isRest = hasRest && arg->pn_next == funBody;
        MOZ_ASSERT_IF(isRest, !initializer);

        bool isDestructuring = !bindingElement->isKind(ParseNodeKind::Name);

        // ES 14.1.19 says if BindingElement contains an expression in the
        // production FormalParameter : BindingElement, it is evaluated in a
        // new var environment. This is needed to prevent vars from escaping
        // direct eval in parameter expressions.
        Maybe<EmitterScope> paramExprVarScope;
        if (funbox->hasDirectEvalInParameterExpr && (isDestructuring || initializer)) {
            paramExprVarScope.emplace(this);
            if (!paramExprVarScope->enterParameterExpressionVar(this))
                return false;
        }

        // First push the RHS if there is a default expression or if it is
        // rest.

        if (initializer) {
            // If we have an initializer, emit the initializer and assign it
            // to the argument slot. TDZ is taken care of afterwards.
            MOZ_ASSERT(hasParameterExprs);
            if (!emitArgOp(JSOP_GETARG, argSlot))
                return false;
            if (!emit1(JSOP_DUP))
                return false;
            if (!emit1(JSOP_UNDEFINED))
                return false;
            if (!emit1(JSOP_STRICTEQ))
                return false;
            // Emit source note to enable Ion compilation.
            if (!newSrcNote(SRC_IF))
                return false;
            JumpList jump;
            if (!emitJump(JSOP_IFEQ, &jump))
                return false;
            if (!emit1(JSOP_POP))
                return false;
            if (!emitInitializerInBranch(initializer, bindingElement))
                return false;
            if (!emitJumpTargetAndPatch(jump))
                return false;
        } else if (isRest) {
            if (!emit1(JSOP_REST))
                return false;
            checkTypeSet(JSOP_REST);
        }

        // Initialize the parameter name.

        if (isDestructuring) {
            // If we had an initializer or the rest parameter, the value is
            // already on the stack.
            if (!initializer && !isRest && !emitArgOp(JSOP_GETARG, argSlot))
                return false;

            // If there's an parameter expression var scope, the destructuring
            // declaration needs to initialize the name in the function scope,
            // which is not the innermost scope.
            if (!emitDestructuringOps(bindingElement,
                                      paramExprVarScope
                                      ? DestructuringFormalParameterInVarScope
                                      : DestructuringDeclaration))
            {
                return false;
            }

            if (!emit1(JSOP_POP)) {
                return false;
            }
        } else if (hasParameterExprs || isRest) {
            RootedAtom paramName(cx, bindingElement->name());
            NameLocation paramLoc = *locationOfNameBoundInScope(paramName, funScope);
            NameOpEmitter noe(this, paramName, paramLoc, NameOpEmitter::Kind::Initialize);
            if (!noe.prepareForRhs()) {
                return false;
            }
            if (hasParameterExprs) {
                // If we had an initializer or a rest parameter, the value is
                // already on the stack.
                if (!initializer && !isRest) {
                    if (!emitArgOp(JSOP_GETARG, argSlot)) {
                        return false;
                    }
                }
            }
            if (!noe.emitAssignment()) {
                return false;
            }
            if (!emit1(JSOP_POP)) {
                return false;
            }
        }

        if (paramExprVarScope) {
            if (!paramExprVarScope->leave(this))
                return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitInitializeFunctionSpecialNames()
{
    FunctionBox* funbox = sc->asFunctionBox();

    auto emitInitializeFunctionSpecialName = [](BytecodeEmitter* bce, HandlePropertyName name,
                                                JSOp op)
    {
        // A special name must be slotful, either on the frame or on the
        // call environment.
        MOZ_ASSERT(bce->lookupName(name).hasKnownSlot());

        NameOpEmitter noe(bce, name, NameOpEmitter::Kind::Initialize);
        if (!noe.prepareForRhs()) {
            return false;
        }
        if (!bce->emit1(op)) {
            return false;
        }
        if (!noe.emitAssignment()) {
            return false;
        }
        if (!bce->emit1(JSOP_POP)) {
            return false;
        }

        return true;
    };

    // Do nothing if the function doesn't have an arguments binding.
    if (funbox->argumentsHasLocalBinding()) {
        if (!emitInitializeFunctionSpecialName(this, cx->names().arguments, JSOP_ARGUMENTS))
            return false;
    }

    // Do nothing if the function doesn't have a this-binding (this
    // happens for instance if it doesn't use this/eval or if it's an
    // arrow function).
    if (funbox->hasThisBinding()) {
        if (!emitInitializeFunctionSpecialName(this, cx->names().dotThis, JSOP_FUNCTIONTHIS))
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitFunctionBody(ParseNode* funBody)
{
    FunctionBox* funbox = sc->asFunctionBox();

    if (!emitTree(funBody))
        return false;

    if (funbox->needsFinalYield()) {
        // If we fall off the end of a generator, do a final yield.
        bool needsIteratorResult = funbox->needsIteratorResult();
        if (needsIteratorResult) {
            if (!emitPrepareIteratorResult())
                return false;
        }

        if (!emit1(JSOP_UNDEFINED))
            return false;

        if (needsIteratorResult) {
            if (!emitFinishIteratorResult(true))
                return false;
        }

        if (!emit1(JSOP_SETRVAL))
            return false;

        if (!emitGetDotGeneratorInInnermostScope())
            return false;

        // No need to check for finally blocks, etc as in EmitReturn.
        if (!emitYieldOp(JSOP_FINALYIELDRVAL))
            return false;
    } else {
        // Non-generator functions just return |undefined|. The
        // JSOP_RETRVAL emitted below will do that, except if the
        // script has a finally block: there can be a non-undefined
        // value in the return value slot. Make sure the return value
        // is |undefined|.
        if (hasTryFinally) {
            if (!emit1(JSOP_UNDEFINED))
                return false;
            if (!emit1(JSOP_SETRVAL))
                return false;
        }
    }

    if (funbox->isDerivedClassConstructor()) {
        if (!emitCheckDerivedClassConstructorReturn())
            return false;
    }

    return true;
}

bool
BytecodeEmitter::emitLexicalInitialization(ParseNode* name)
{
    return emitLexicalInitialization(name->name());
}

bool
BytecodeEmitter::emitLexicalInitialization(JSAtom* name)
{
    NameOpEmitter noe(this, name, NameOpEmitter::Kind::Initialize);
    if (!noe.prepareForRhs()) {
        return false;
    }

    // The caller has pushed the RHS to the top of the stack. Assert that the
    // name is lexical and no BIND[G]NAME ops were emitted.
    MOZ_ASSERT(noe.loc().isLexical());
    MOZ_ASSERT(!noe.emittedBindOp());

    if (!noe.emitAssignment()) {
        return false;
    }

    return true;
}

static MOZ_ALWAYS_INLINE
CodeNode* FindConstructor(JSContext* cx, ListNode* classMethods)
{
    for (ParseNode* mn = classMethods->pn_head; mn; mn = mn->pn_next) {
        ClassMethod& method = mn->as<ClassMethod>();
        ParseNode& methodName = method.name();
        if (!method.isStatic() &&
            (methodName.isKind(ParseNodeKind::ObjectPropertyName) ||
             methodName.isKind(ParseNodeKind::String)) &&
             methodName.pn_atom == cx->names().constructor) {
            return &method.method().as<CodeNode>();
        }
    }

    return nullptr;
}

// This follows ES6 14.5.14 (ClassDefinitionEvaluation) and ES6 14.5.15
// (BindingClassDeclarationEvaluation).
bool
BytecodeEmitter::emitClass(ParseNode* pn,
                           ClassNameKind nameKind /* = ClassNameKind::BindingName */,
                           HandleAtom nameForAnonymousClass /* = nullptr */)
{
    MOZ_ASSERT((nameKind == ClassNameKind::InferredName) ==
               (nameForAnonymousClass != nullptr));

    ClassNode& classNode = pn->as<ClassNode>();

    ParseNode* heritageExpression = classNode.heritage();
    ListNode* classMethods = &classNode.methodList()->as<ListNode>();
    CodeNode* constructor = FindConstructor(cx, classMethods);

    // If |nameKind != ClassNameKind::ComputedName|
    //                [stack]
    // Else
    //                [stack] NAME

    ClassEmitter ce(this);
    RootedAtom innerName(cx);
    ClassEmitter::Kind kind = ClassEmitter::Kind::Expression;
    if (ClassNames* names = classNode.names()) {
        MOZ_ASSERT(nameKind == ClassNameKind::BindingName);
        innerName = names->innerBinding()->name();
        MOZ_ASSERT(innerName);

        if (names->outerBinding()) {
            MOZ_ASSERT(names->outerBinding()->name());
            MOZ_ASSERT(names->outerBinding()->name() == innerName);
            kind = ClassEmitter::Kind::Declaration;
        }

        if (!ce.emitScopeForNamedClass(classNode.scopeBindings())) {
            //            [stack]
            return false;
        }
    }

    // This is kind of silly. In order to the get the home object defined on
    // the constructor, we have to make it second, but we want the prototype
    // on top for EmitPropertyList, because we expect static properties to be
    // rarer. The result is a few more swaps than we would like. Such is life.
    bool isDerived = !!heritageExpression;
    bool hasNameOnStack = nameKind == ClassNameKind::ComputedName;
    if (isDerived) {
        if (!emitTree(heritageExpression)) {
            //            [stack] HERITAGE
            return false;
        }
        if (!ce.emitDerivedClass(innerName, nameForAnonymousClass,
                                 hasNameOnStack)) {
            //            [stack] HERITAGE HOMEOBJ
            return false;
        }
    } else {
        if (!ce.emitClass(innerName, nameForAnonymousClass, hasNameOnStack)) {
            //            [stack] HOMEOBJ
            return false;
        }
    }

    // Stack currently has HOMEOBJ followed by optional HERITAGE. When HERITAGE
    // is not used, an implicit value of %FunctionPrototype% is implied.
    if (constructor) {
        bool needsHomeObject = constructor->pn_funbox->needsHomeObject();
        // HERITAGE is consumed inside emitFunction.
        if (!emitFunction(constructor, isDerived)) {
            //            [stack] HOMEOBJ CTOR
            return false;
        }
        if (nameKind == ClassNameKind::InferredName) {
            if (!setFunName(constructor->pn_funbox->function(),
                            nameForAnonymousClass)) {
                return false;
            }
        }
        if (!ce.emitInitConstructor(needsHomeObject)) {
            //            [stack] CTOR HOMEOBJ
            return false;
        }
    } else {
        if (!ce.emitInitDefaultConstructor(Some(classNode.pn_pos.begin),
            Some(classNode.pn_pos.end))) {
            //            [stack] CTOR HOMEOBJ
            return false;
        }
    }
    if (!emitPropertyList(classMethods, ce, ClassBody)) {
        //              [stack] CTOR HOMEOBJ
        return false;
    }
    if (!ce.emitEnd(kind)) {
        //              [stack] # class declaration
        //              [stack]
        //              [stack] # class expression
        //              [stack] CTOR
        return false;
    }

    return true;
}

bool
BytecodeEmitter::emitExportDefault(ParseNode* pn)
{
    MOZ_ASSERT(pn->isKind(ParseNodeKind::ExportDefault));

    ParseNode* valueNode = pn->pn_left;
    if (valueNode->isDirectRHSAnonFunction()) {
        MOZ_ASSERT(pn->pn_right);

        HandlePropertyName name = cx->names().default_;
        if (!emitAnonymousFunctionWithName(valueNode, name)) {
            return false;
        }
    } else {
        if (!emitTree(valueNode)) {
            return false;
        }
    }

    if (ParseNode* binding = pn->pn_right) {
        if (!emitLexicalInitialization(&binding->as<NameNode>())) {
            return false;
        }

        if (!emit1(JSOP_POP)) {
            return false;
        }
    }

    return true;
}

bool
BytecodeEmitter::emitTree(ParseNode* pn, ValueUsage valueUsage /* = ValueUsage::WantValue */,
                          EmitLineNumberNote emitLineNote /* = EMIT_LINENOTE */)
{
    if (!CheckRecursionLimit(cx))
        return false;

    EmitLevelManager elm(this);

    /* Emit notes to tell the current bytecode's source line number.
       However, a couple trees require special treatment; see the
       relevant emitter functions for details. */
    if (emitLineNote == EMIT_LINENOTE && !ParseNodeRequiresSpecialLineNumberNotes(pn)) {
        if (!updateLineNumberNotes(pn->pn_pos.begin))
            return false;
    }

    switch (pn->getKind()) {
      case ParseNodeKind::Function:
        if (!emitFunction(pn))
            return false;
        break;

      case ParseNodeKind::ParamsBody:
        if (!emitFunctionFormalParametersAndBody(pn))
            return false;
        break;

      case ParseNodeKind::If:
        if (!emitIf(pn))
            return false;
        break;

      case ParseNodeKind::Switch:
        if (!emitSwitch(pn))
            return false;
        break;

      case ParseNodeKind::While:
        if (!emitWhile(pn))
            return false;
        break;

      case ParseNodeKind::DoWhile:
        if (!emitDo(pn))
            return false;
        break;

      case ParseNodeKind::For:
        if (!emitFor(pn))
            return false;
        break;

      case ParseNodeKind::ComprehensionFor:
        if (!emitComprehensionFor(pn))
            return false;
        break;

      case ParseNodeKind::Break:
        if (!emitBreak(pn->as<BreakStatement>().label()))
            return false;
        break;

      case ParseNodeKind::Continue:
        if (!emitContinue(pn->as<ContinueStatement>().label()))
            return false;
        break;

      case ParseNodeKind::With:
        if (!emitWith(pn))
            return false;
        break;

      case ParseNodeKind::Try:
        if (!emitTry(pn))
            return false;
        break;

      case ParseNodeKind::Catch:
        if (!emitCatch(pn))
            return false;
        break;

      case ParseNodeKind::Var:
        if (!emitDeclarationList(pn))
            return false;
        break;

      case ParseNodeKind::Return:
        if (!emitReturn(pn))
            return false;
        break;

      case ParseNodeKind::YieldStar:
        if (!emitYieldStar(pn->pn_kid))
            return false;
        break;

      case ParseNodeKind::Generator:
        if (!emit1(JSOP_GENERATOR))
            return false;
        break;

      case ParseNodeKind::InitialYield:
        if (!emitInitialYield(pn))
            return false;
        break;

      case ParseNodeKind::Yield:
        if (!emitYield(pn))
            return false;
        break;

      case ParseNodeKind::Await:
        if (!emitAwaitInInnermostScope(pn))
            return false;
        break;

      case ParseNodeKind::StatementList:
        if (!emitStatementList(pn))
            return false;
        break;

      case ParseNodeKind::EmptyStatement:
        break;

      case ParseNodeKind::ExpressionStatement:
        if (!emitExpressionStatement(pn))
            return false;
        break;

      case ParseNodeKind::Label:
        if (!emitLabeledStatement(&pn->as<LabeledStatement>()))
            return false;
        break;

      case ParseNodeKind::Comma:
        if (!emitSequenceExpr(pn, valueUsage))
            return false;
        break;

      case ParseNodeKind::Assign:
      case ParseNodeKind::AddAssign:
      case ParseNodeKind::SubAssign:
      case ParseNodeKind::BitOrAssign:
      case ParseNodeKind::BitXorAssign:
      case ParseNodeKind::BitAndAssign:
      case ParseNodeKind::LshAssign:
      case ParseNodeKind::RshAssign:
      case ParseNodeKind::UrshAssign:
      case ParseNodeKind::MulAssign:
      case ParseNodeKind::DivAssign:
      case ParseNodeKind::ModAssign:
      case ParseNodeKind::PowAssign:
        if (!emitAssignment(pn->pn_left,
                            CompoundAssignmentParseNodeKindToJSOp(pn->getKind()),
                            pn->pn_right))
        {
            return false;
        }
        break;

      case ParseNodeKind::CoalesceAssignExpr:
      case ParseNodeKind::OrAssignExpr:
      case ParseNodeKind::AndAssignExpr:
        if (!emitShortCircuitAssignment(pn)) {
          return false;
        }
        break;

      case ParseNodeKind::Conditional:
        if (!emitConditionalExpression(pn->as<ConditionalExpression>(), valueUsage))
            return false;
        break;

      case ParseNodeKind::Or:
      case ParseNodeKind::CoalesceExpr:
      case ParseNodeKind::And:
        if (!emitShortCircuit(pn))
            return false;
        break;

      case ParseNodeKind::Add:
      case ParseNodeKind::Sub:
      case ParseNodeKind::BitOr:
      case ParseNodeKind::BitXor:
      case ParseNodeKind::BitAnd:
      case ParseNodeKind::StrictEq:
      case ParseNodeKind::Eq:
      case ParseNodeKind::StrictNe:
      case ParseNodeKind::Ne:
      case ParseNodeKind::Lt:
      case ParseNodeKind::Le:
      case ParseNodeKind::Gt:
      case ParseNodeKind::Ge:
      case ParseNodeKind::In:
      case ParseNodeKind::InstanceOf:
      case ParseNodeKind::Lsh:
      case ParseNodeKind::Rsh:
      case ParseNodeKind::Ursh:
      case ParseNodeKind::Star:
      case ParseNodeKind::Div:
      case ParseNodeKind::Mod:
        if (!emitLeftAssociative(pn))
            return false;
        break;

      case ParseNodeKind::Pow:
        if (!emitRightAssociative(pn))
            return false;
        break;

      case ParseNodeKind::Pipeline:
        if (!emitPipeline(pn))
            return false;
        break;

      case ParseNodeKind::TypeOfName:
        if (!emitTypeof(pn, JSOP_TYPEOF))
            return false;
        break;

      case ParseNodeKind::TypeOfExpr:
        if (!emitTypeof(pn, JSOP_TYPEOFEXPR))
            return false;
        break;

      case ParseNodeKind::Throw:
      case ParseNodeKind::Void:
      case ParseNodeKind::Not:
      case ParseNodeKind::BitNot:
      case ParseNodeKind::Pos:
      case ParseNodeKind::Neg:
        if (!emitUnary(pn))
            return false;
        break;

      case ParseNodeKind::PreIncrement:
      case ParseNodeKind::PreDecrement:
      case ParseNodeKind::PostIncrement:
      case ParseNodeKind::PostDecrement:
        if (!emitIncOrDec(pn))
            return false;
        break;

      case ParseNodeKind::DeleteName:
        if (!emitDeleteName(pn))
            return false;
        break;

      case ParseNodeKind::DeleteProp:
        if (!emitDeleteProperty(pn))
            return false;
        break;

      case ParseNodeKind::DeleteElem:
        if (!emitDeleteElement(pn))
            return false;
        break;

      case ParseNodeKind::DeleteExpr:
        if (!emitDeleteExpression(pn))
            return false;
        break;

      case ParseNodeKind::DeleteOptionalChain:
        if (!emitDeleteOptionalChain(pn))
          return false;
        break;
  
      case ParseNodeKind::OptionalChain:
        if (!emitOptionalChain(pn, valueUsage))
          return false;
        break;

      case ParseNodeKind::Dot: {
        PropertyAccess* prop = &pn->as<PropertyAccess>();
        bool isSuper = prop->isSuper();
        PropOpEmitter poe(this,
                          PropOpEmitter::Kind::Get,
                          isSuper
                          ? PropOpEmitter::ObjKind::Super
                          : PropOpEmitter::ObjKind::Other);
        if (!poe.prepareForObj()) {
            return false;
        }
        if (isSuper) {
            UnaryNode* base = &prop->expression().as<UnaryNode>();
            if (!emitGetThisForSuperBase(base)) {         // THIS
                return false;
            }
        } else {
            if (!emitPropLHS(prop)) {                     // OBJ
                return false;
            }
        }
        if (!poe.emitGet(prop->key().pn_atom)) {          // PROP
            return false;
        }
        break;
      }
      case ParseNodeKind::Elem: {
        PropertyByValue* elem = &pn->as<PropertyByValue>();
        bool isSuper = elem->isSuper();
        ElemOpEmitter eoe(this,
                          ElemOpEmitter::Kind::Get,
                          isSuper
                          ? ElemOpEmitter::ObjKind::Super
                          : ElemOpEmitter::ObjKind::Other);
        if (!emitElemObjAndKey(elem, isSuper, eoe)) {     // [Super]
            //                                            // THIS KEY
            //                                            // [Other]
            //                                            // OBJ KEY
            return false;
        }
        if (!eoe.emitGet()) {                             // ELEM
            return false;
        }

        break;
      }

      case ParseNodeKind::New:
      case ParseNodeKind::TaggedTemplate:
      case ParseNodeKind::Call:
      case ParseNodeKind::GenExp:
      case ParseNodeKind::SuperCall:
        if (!emitCallOrNew(pn, valueUsage))
            return false;
        break;

      case ParseNodeKind::LexicalScope:
        if (!emitLexicalScope(pn))
            return false;
        break;

      case ParseNodeKind::Const:
      case ParseNodeKind::Let:
        if (!emitDeclarationList(pn))
            return false;
        break;

      case ParseNodeKind::Import:
        MOZ_ASSERT(sc->isModuleContext());
        break;

      case ParseNodeKind::Export:
        MOZ_ASSERT(sc->isModuleContext());
        if (pn->pn_kid->getKind() !=ParseNodeKind::ExportSpecList) {
            if (!emitTree(pn->pn_kid))
                return false;
        }
        break;

      case ParseNodeKind::ExportDefault:
        MOZ_ASSERT(sc->isModuleContext());
        if (!emitExportDefault(pn))
            return false;
        break;

      case ParseNodeKind::ExportFrom:
        MOZ_ASSERT(sc->isModuleContext());
        break;

      case ParseNodeKind::ArrayPush:
        /*
         * The array object's stack index is in arrayCompDepth. See below
         * under the array initialiser code generator for array comprehension
         * special casing.
         */
        if (!emitTree(pn->pn_kid))
            return false;
        if (!emitDupAt(this->stackDepth - 1 - arrayCompDepth))
            return false;
        if (!emit1(JSOP_ARRAYPUSH))
            return false;
        break;

      case ParseNodeKind::CallSiteObj:
        if (!emitCallSiteObject(pn))
            return false;
        break;

      case ParseNodeKind::Array:
        if (!emitArrayLiteral(pn))
            return false;
        break;

      case ParseNodeKind::ArrayComp:
        if (!emitArrayComp(pn))
            return false;
        break;

      case ParseNodeKind::Object:
        if (!emitObject(pn))
            return false;
        break;

      case ParseNodeKind::Name:
        if (!emitGetName(pn))
            return false;
        break;

      case ParseNodeKind::TemplateStringList:
        if (!emitTemplateString(pn))
            return false;
        break;

      case ParseNodeKind::TemplateString:
      case ParseNodeKind::String:
        if (!emitAtomOp(pn->pn_atom, JSOP_STRING))
            return false;
        break;

      case ParseNodeKind::Number:
        if (!emitNumberOp(pn->pn_dval))
            return false;
        break;

      case ParseNodeKind::RegExp:
        if (!emitRegExp(objectList.add(pn->as<RegExpLiteral>().objbox())))
            return false;
        break;

      case ParseNodeKind::True:
      case ParseNodeKind::False:
      case ParseNodeKind::Null:
      case ParseNodeKind::RawUndefined:
        if (!emit1(pn->getOp()))
            return false;
        break;

      case ParseNodeKind::This:
        if (!emitThisLiteral(pn))
            return false;
        break;

      case ParseNodeKind::Debugger:
        if (!updateSourceCoordNotes(pn->pn_pos.begin))
            return false;
        if (!emit1(JSOP_DEBUGGER))
            return false;
        break;

      case ParseNodeKind::Class:
        if (!emitClass(pn))
            return false;
        break;

      case ParseNodeKind::NewTarget:
        if (!emit1(JSOP_NEWTARGET))
            return false;
        break;

      case ParseNodeKind::ImportMeta:
        if (!emit1(JSOP_IMPORTMETA))
            return false;
        break;

      case ParseNodeKind::CallImport:
        if (!emitTree(pn->pn_right) || !emit1(JSOP_DYNAMIC_IMPORT)) {
            return false;
        }
        break;

      case ParseNodeKind::SetThis:
        if (!emitSetThis(pn))
            return false;
        break;

      case ParseNodeKind::PropertyName:
      case ParseNodeKind::PosHolder:
        MOZ_FALLTHROUGH_ASSERT("Should never try to emit ParseNodeKind::PosHolder or ::Property");

      default:
        MOZ_ASSERT(0);
    }

    /* bce->emitLevel == 1 means we're last on the stack, so finish up. */
    if (emitLevel == 1) {
        if (!updateSourceCoordNotes(pn->pn_pos.end))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::emitTreeInBranch(ParseNode* pn,
                                  ValueUsage valueUsage /* = ValueUsage::WantValue */)
{
    // Code that may be conditionally executed always need their own TDZ
    // cache.
    TDZCheckCache tdzCache(this);
    return emitTree(pn, valueUsage);
}

static bool
AllocSrcNote(JSContext* cx, SrcNotesVector& notes, unsigned* index)
{
    size_t oldLength = notes.length();

    if (MOZ_UNLIKELY(oldLength + 1 > MaxSrcNotesLength)) {
        ReportAllocationOverflow(cx);
        return false;
    }


    if (!notes.growBy(1)) {
        return false;
    }

    *index = oldLength;;
    return true;
}

bool
BytecodeEmitter::newSrcNote(SrcNoteType type, unsigned* indexp)
{
    SrcNotesVector& notes = this->notes();
    unsigned index;
    if (!AllocSrcNote(cx, notes, &index))
        return false;

    /*
     * Compute delta from the last annotated bytecode's offset.  If it's too
     * big to fit in sn, allocate one or more xdelta notes and reset sn.
     */
    ptrdiff_t offset = this->offset();
    ptrdiff_t delta = offset - lastNoteOffset();
    current->lastNoteOffset = offset;
    if (delta >= SN_DELTA_LIMIT) {
        do {
            ptrdiff_t xdelta = Min(delta, SN_XDELTA_MASK);
            SN_MAKE_XDELTA(&notes[index], xdelta);
            delta -= xdelta;
            if (!AllocSrcNote(cx, notes, &index))
                return false;
        } while (delta >= SN_DELTA_LIMIT);
    }

    /*
     * Initialize type and delta, then allocate the minimum number of notes
     * needed for type's arity.  Usually, we won't need more, but if an offset
     * does take two bytes, setSrcNoteOffset will grow notes.
     */
    SN_MAKE_NOTE(&notes[index], type, delta);
    for (int n = (int)js_SrcNoteSpec[type].arity; n > 0; n--) {
        if (!newSrcNote(SRC_NULL))
            return false;
    }

    if (indexp)
        *indexp = index;
    return true;
}

bool
BytecodeEmitter::newSrcNote2(SrcNoteType type, ptrdiff_t offset, unsigned* indexp)
{
    unsigned index;
    if (!newSrcNote(type, &index))
        return false;
    if (!setSrcNoteOffset(index, 0, offset))
        return false;
    if (indexp)
        *indexp = index;
    return true;
}

bool
BytecodeEmitter::newSrcNote3(SrcNoteType type, ptrdiff_t offset1, ptrdiff_t offset2,
                             unsigned* indexp)
{
    unsigned index;
    if (!newSrcNote(type, &index))
        return false;
    if (!setSrcNoteOffset(index, 0, offset1))
        return false;
    if (!setSrcNoteOffset(index, 1, offset2))
        return false;
    if (indexp)
        *indexp = index;
    return true;
}

bool
BytecodeEmitter::addToSrcNoteDelta(jssrcnote* sn, ptrdiff_t delta)
{
    /*
     * Called only from finishTakingSrcNotes to add to main script note
     * deltas, and only by a small positive amount.
     */
    MOZ_ASSERT(current == &main);
    MOZ_ASSERT((unsigned) delta < (unsigned) SN_XDELTA_LIMIT);

    ptrdiff_t base = SN_DELTA(sn);
    ptrdiff_t limit = SN_IS_XDELTA(sn) ? SN_XDELTA_LIMIT : SN_DELTA_LIMIT;
    ptrdiff_t newdelta = base + delta;
    if (newdelta < limit) {
        SN_SET_DELTA(sn, newdelta);
    } else {
        jssrcnote xdelta;
        SN_MAKE_XDELTA(&xdelta, delta);
        if (!main.notes.insert(sn, xdelta))
            return false;
    }
    return true;
}

bool
BytecodeEmitter::setSrcNoteOffset(unsigned index, unsigned which, ptrdiff_t offset)
{
    if (!SN_REPRESENTABLE_OFFSET(offset)) {
        parser.reportError(JSMSG_NEED_DIET, js_script_str);
        return false;
    }

    SrcNotesVector& notes = this->notes();

    /* Find the offset numbered which (i.e., skip exactly which offsets). */
    jssrcnote* sn = &notes[index];
    MOZ_ASSERT(SN_TYPE(sn) != SRC_XDELTA);
    MOZ_ASSERT((int) which < js_SrcNoteSpec[SN_TYPE(sn)].arity);
    for (sn++; which; sn++, which--) {
        if (*sn & SN_4BYTE_OFFSET_FLAG)
            sn += 3;
    }

    /*
     * See if the new offset requires four bytes either by being too big or if
     * the offset has already been inflated (in which case, we need to stay big
     * to not break the srcnote encoding if this isn't the last srcnote).
     */
    if (offset > (ptrdiff_t)SN_4BYTE_OFFSET_MASK || (*sn & SN_4BYTE_OFFSET_FLAG)) {
        /* Maybe this offset was already set to a four-byte value. */
        if (!(*sn & SN_4BYTE_OFFSET_FLAG)) {
            /* Insert three dummy bytes that will be overwritten shortly. */
            if (MOZ_UNLIKELY(notes.length() + 3 > MaxSrcNotesLength)) {
                ReportAllocationOverflow(cx);
                return false;
            }
            jssrcnote dummy = 0;
            if (!(sn = notes.insert(sn, dummy)) ||
                !(sn = notes.insert(sn, dummy)) ||
                !(sn = notes.insert(sn, dummy)))
            {
                return false;
            }
        }
        *sn++ = (jssrcnote)(SN_4BYTE_OFFSET_FLAG | (offset >> 24));
        *sn++ = (jssrcnote)(offset >> 16);
        *sn++ = (jssrcnote)(offset >> 8);
    }
    *sn = (jssrcnote)offset;
    return true;
}

bool
BytecodeEmitter::finishTakingSrcNotes(uint32_t* out)
{
    MOZ_ASSERT(current == &main);

    unsigned prologueCount = prologue.notes.length();
    if (prologueCount && prologue.currentLine != firstLine) {
        switchToPrologue();
        if (!newSrcNote2(SRC_SETLINE, ptrdiff_t(firstLine)))
            return false;
        switchToMain();
    } else {
        /*
         * Either no prologue srcnotes, or no line number change over prologue.
         * We don't need a SRC_SETLINE, but we may need to adjust the offset
         * of the first main note, by adding to its delta and possibly even
         * prepending SRC_XDELTA notes to it to account for prologue bytecodes
         * that came at and after the last annotated bytecode.
         */
        ptrdiff_t offset = prologueOffset() - prologue.lastNoteOffset;
        MOZ_ASSERT(offset >= 0);
        if (offset > 0 && main.notes.length() != 0) {
            /* NB: Use as much of the first main note's delta as we can. */
            jssrcnote* sn = main.notes.begin();
            ptrdiff_t delta = SN_IS_XDELTA(sn)
                            ? SN_XDELTA_MASK - (*sn & SN_XDELTA_MASK)
                            : SN_DELTA_MASK - (*sn & SN_DELTA_MASK);
            if (offset < delta)
                delta = offset;
            for (;;) {
                if (!addToSrcNoteDelta(sn, delta))
                    return false;
                offset -= delta;
                if (offset == 0)
                    break;
                delta = Min(offset, SN_XDELTA_MASK);
                sn = main.notes.begin();
            }
        }
    }

    // The prologue count might have changed, so we can't reuse prologueCount.
    // The + 1 is to account for the final SN_MAKE_TERMINATOR that is appended
    // when the notes are copied to their final destination by CopySrcNotes.
    *out = prologue.notes.length() + main.notes.length() + 1;
    return true;
}

void
BytecodeEmitter::copySrcNotes(jssrcnote* destination, uint32_t nsrcnotes)
{
    unsigned prologueCount = prologue.notes.length();
    unsigned mainCount = main.notes.length();
    unsigned totalCount = prologueCount + mainCount;
    MOZ_ASSERT(totalCount == nsrcnotes - 1);
    if (prologueCount)
        PodCopy(destination, prologue.notes.begin(), prologueCount);
    PodCopy(destination + prologueCount, main.notes.begin(), mainCount);
    SN_MAKE_TERMINATOR(&destination[totalCount]);
}

void
CGConstList::finish(ConstArray* array)
{
    MOZ_ASSERT(length() == array->length);

    for (unsigned i = 0; i < length(); i++)
        array->vector[i] = list[i];
}

/*
 * Find the index of the given object for code generator.
 *
 * Since the emitter refers to each parsed object only once, for the index we
 * use the number of already indexed objects. We also add the object to a list
 * to convert the list to a fixed-size array when we complete code generation,
 * see js::CGObjectList::finish below.
 */
unsigned
CGObjectList::add(ObjectBox* objbox)
{
    MOZ_ASSERT(!objbox->emitLink);
    objbox->emitLink = lastbox;
    lastbox = objbox;
    return length++;
}

void
CGObjectList::finish(ObjectArray* array)
{
    MOZ_ASSERT(length <= INDEX_LIMIT);
    MOZ_ASSERT(length == array->length);

    js::GCPtrObject* cursor = array->vector + array->length;
    ObjectBox* objbox = lastbox;
    do {
        --cursor;
        MOZ_ASSERT(!*cursor);
        MOZ_ASSERT(objbox->object->isTenured());
        *cursor = objbox->object;
    } while ((objbox = objbox->emitLink) != nullptr);
    MOZ_ASSERT(cursor == array->vector);
}

void
CGScopeList::finish(ScopeArray* array)
{
    MOZ_ASSERT(length() <= INDEX_LIMIT);
    MOZ_ASSERT(length() == array->length);
    for (uint32_t i = 0; i < length(); i++)
        array->vector[i].init(vector[i]);
}

bool
CGTryNoteList::append(JSTryNoteKind kind, uint32_t stackDepth, size_t start, size_t end)
{
    MOZ_ASSERT(start <= end);
    MOZ_ASSERT(size_t(uint32_t(start)) == start);
    MOZ_ASSERT(size_t(uint32_t(end)) == end);

    JSTryNote note;
    note.kind = kind;
    note.stackDepth = stackDepth;
    note.start = uint32_t(start);
    note.length = uint32_t(end - start);

    return list.append(note);
}

void
CGTryNoteList::finish(TryNoteArray* array)
{
    MOZ_ASSERT(length() == array->length);

    for (unsigned i = 0; i < length(); i++)
        array->vector[i] = list[i];
}

bool
CGScopeNoteList::append(uint32_t scopeIndex, uint32_t offset, bool inPrologue,
                        uint32_t parent)
{
    CGScopeNote note;
    mozilla::PodZero(&note);

    note.index = scopeIndex;
    note.start = offset;
    note.parent = parent;
    note.startInPrologue = inPrologue;

    return list.append(note);
}

void
CGScopeNoteList::recordEnd(uint32_t index, uint32_t offset, bool inPrologue)
{
    MOZ_ASSERT(index < length());
    MOZ_ASSERT(list[index].length == 0);
    list[index].end = offset;
    list[index].endInPrologue = inPrologue;
}

void
CGScopeNoteList::finish(ScopeNoteArray* array, uint32_t prologueLength)
{
    MOZ_ASSERT(length() == array->length);

    for (unsigned i = 0; i < length(); i++) {
        if (!list[i].startInPrologue)
            list[i].start += prologueLength;
        if (!list[i].endInPrologue && list[i].end != UINT32_MAX)
            list[i].end += prologueLength;
        MOZ_ASSERT(list[i].end >= list[i].start);
        list[i].length = list[i].end - list[i].start;
        array->vector[i] = list[i];
    }
}

void
CGYieldAndAwaitOffsetList::finish(YieldAndAwaitOffsetArray& array, uint32_t prologueLength)
{
    MOZ_ASSERT(length() == array.length());

    for (unsigned i = 0; i < length(); i++)
        array[i] = prologueLength + list[i];
}

/*
 * We should try to get rid of offsetBias (always 0 or 1, where 1 is
 * JSOP_{NOP,POP}_LENGTH), which is used only by SRC_FOR.
 */
const JSSrcNoteSpec js_SrcNoteSpec[] = {
#define DEFINE_SRC_NOTE_SPEC(sym, name, arity) { name, arity },
    FOR_EACH_SRC_NOTE_TYPE(DEFINE_SRC_NOTE_SPEC)
#undef DEFINE_SRC_NOTE_SPEC
};

static int
SrcNoteArity(jssrcnote* sn)
{
    MOZ_ASSERT(SN_TYPE(sn) < SRC_LAST);
    return js_SrcNoteSpec[SN_TYPE(sn)].arity;
}

JS_FRIEND_API(unsigned)
js::SrcNoteLength(jssrcnote* sn)
{
    unsigned arity;
    jssrcnote* base;

    arity = SrcNoteArity(sn);
    for (base = sn++; arity; sn++, arity--) {
        if (*sn & SN_4BYTE_OFFSET_FLAG)
            sn += 3;
    }
    return sn - base;
}

JS_FRIEND_API(ptrdiff_t)
js::GetSrcNoteOffset(jssrcnote* sn, unsigned which)
{
    /* Find the offset numbered which (i.e., skip exactly which offsets). */
    MOZ_ASSERT(SN_TYPE(sn) != SRC_XDELTA);
    MOZ_ASSERT((int) which < SrcNoteArity(sn));
    for (sn++; which; sn++, which--) {
        if (*sn & SN_4BYTE_OFFSET_FLAG)
            sn += 3;
    }
    if (*sn & SN_4BYTE_OFFSET_FLAG) {
        return (ptrdiff_t)(((uint32_t)(sn[0] & SN_4BYTE_OFFSET_MASK) << 24)
                           | (sn[1] << 16)
                           | (sn[2] << 8)
                           | sn[3]);
    }
    return (ptrdiff_t)*sn;
}
