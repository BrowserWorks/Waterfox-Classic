/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef vm_GlobalObject_h
#define vm_GlobalObject_h

#include "jsarray.h"
#include "jsbool.h"
#include "jsexn.h"
#include "jsfun.h"
#include "jsnum.h"

#include "js/Vector.h"
#include "vm/ArrayBufferObject.h"
#include "vm/ErrorObject.h"
#include "vm/RegExpStatics.h"
#include "vm/Runtime.h"

namespace js {

class Debugger;
class TypedObjectModuleObject;
class LexicalEnvironmentObject;

class SimdTypeDescr;
enum class SimdType;

/*
 * Global object slots are reserved as follows:
 *
 * [0, APPLICATION_SLOTS)
 *   Pre-reserved slots in all global objects set aside for the embedding's
 *   use. As with all reserved slots these start out as UndefinedValue() and
 *   are traced for GC purposes. Apart from that the engine never touches
 *   these slots, so the embedding can do whatever it wants with them.
 * [APPLICATION_SLOTS, APPLICATION_SLOTS + JSProto_LIMIT)
 *   Stores the original value of the constructor for the corresponding
 *   JSProtoKey.
 * [APPLICATION_SLOTS + JSProto_LIMIT, APPLICATION_SLOTS + 2 * JSProto_LIMIT)
 *   Stores the prototype, if any, for the constructor for the corresponding
 *   JSProtoKey offset from JSProto_LIMIT.
 * [APPLICATION_SLOTS + 2 * JSProto_LIMIT, RESERVED_SLOTS)
 *   Various one-off values: ES5 13.2.3's [[ThrowTypeError]], RegExp statics,
 *   the original eval for this global object (implementing |var eval =
 *   otherWindow.eval; eval(...)| as an indirect eval), a bit indicating
 *   whether this object has been cleared (see JS_ClearScope), and a cache for
 *   whether eval is allowed (per the global's Content Security Policy).
 *
 * The two JSProto_LIMIT-sized ranges are necessary to implement
 * js::FindClassObject, and spec language speaking in terms of "the original
 * Array prototype object", or "as if by the expression new Array()" referring
 * to the original Array constructor. The actual (writable and even deletable)
 * Object, Array, &c. properties are not stored in reserved slots.
 */
class GlobalObject : public NativeObject
{
    /* Count of slots set aside for application use. */
    static const unsigned APPLICATION_SLOTS = JSCLASS_GLOBAL_APPLICATION_SLOTS;

    /*
     * Count of slots to store built-in prototypes and initial visible
     * properties for the constructors.
     */
    static const unsigned STANDARD_CLASS_SLOTS = JSProto_LIMIT * 2;

    enum : unsigned {
        /* Various function values needed by the engine. */
        EVAL = APPLICATION_SLOTS + STANDARD_CLASS_SLOTS,
        THROWTYPEERROR,

        /* One-off properties stored after slots for built-ins. */
        LEXICAL_ENVIRONMENT,
        EMPTY_GLOBAL_SCOPE,
        ITERATOR_PROTO,
        ARRAY_ITERATOR_PROTO,
        STRING_ITERATOR_PROTO,
        REGEXP_STRING_ITERATOR_PROTO,
        LEGACY_GENERATOR_OBJECT_PROTO,
        STAR_GENERATOR_OBJECT_PROTO,
        STAR_GENERATOR_FUNCTION_PROTO,
        STAR_GENERATOR_FUNCTION,
        ASYNC_FUNCTION_PROTO,
        ASYNC_FUNCTION,
        ASYNC_ITERATOR_PROTO,
        ASYNC_FROM_SYNC_ITERATOR_PROTO,
        ASYNC_GENERATOR,
        ASYNC_GENERATOR_FUNCTION,
        ASYNC_GENERATOR_PROTO,
        MAP_ITERATOR_PROTO,
        SET_ITERATOR_PROTO,
        COLLATOR_PROTO,
        NUMBER_FORMAT,
        NUMBER_FORMAT_PROTO,
        DATE_TIME_FORMAT,
        DATE_TIME_FORMAT_PROTO,
        PLURAL_RULES_PROTO,
        RELATIVE_TIME_FORMAT_PROTO,
        MODULE_PROTO,
        IMPORT_ENTRY_PROTO,
        EXPORT_ENTRY_PROTO,
        REQUESTED_MODULE_PROTO,
        REGEXP_STATICS,
        RUNTIME_CODEGEN_ENABLED,
        DEBUGGERS,
        INTRINSICS,
        FOR_OF_PIC_CHAIN,
        WINDOW_PROXY,
        GLOBAL_THIS_RESOLVED,

        /* Total reserved-slot count for global objects. */
        RESERVED_SLOTS
    };

    /*
     * The slot count must be in the public API for JSCLASS_GLOBAL_FLAGS, and
     * we won't expose GlobalObject, so just assert that the two values are
     * synchronized.
     */
    static_assert(JSCLASS_GLOBAL_SLOT_COUNT == RESERVED_SLOTS,
                  "global object slot counts are inconsistent");

  public:
    LexicalEnvironmentObject& lexicalEnvironment() const;
    GlobalScope& emptyGlobalScope() const;

    void setThrowTypeError(JSFunction* fun) {
        MOZ_ASSERT(getSlotRef(THROWTYPEERROR).isUndefined());
        setSlot(THROWTYPEERROR, ObjectValue(*fun));
    }

    void setOriginalEval(JSObject* evalobj) {
        MOZ_ASSERT(getSlotRef(EVAL).isUndefined());
        setSlot(EVAL, ObjectValue(*evalobj));
    }

    Value getConstructor(JSProtoKey key) const {
        MOZ_ASSERT(key <= JSProto_LIMIT);
        return getSlot(APPLICATION_SLOTS + key);
    }
    static bool skipDeselectedConstructor(JSContext* cx, JSProtoKey key);
    static bool ensureConstructor(JSContext* cx, Handle<GlobalObject*> global, JSProtoKey key);
    static bool resolveConstructor(JSContext* cx, Handle<GlobalObject*> global, JSProtoKey key);
    static bool initBuiltinConstructor(JSContext* cx, Handle<GlobalObject*> global,
                                       JSProtoKey key, HandleObject ctor, HandleObject proto);
    static bool maybeResolveGlobalThis(JSContext* cx, Handle<GlobalObject*> global, bool* resolved);

    void setConstructor(JSProtoKey key, const Value& v) {
        MOZ_ASSERT(key <= JSProto_LIMIT);
        setSlot(APPLICATION_SLOTS + key, v);
    }

    Value getPrototype(JSProtoKey key) const {
        MOZ_ASSERT(key <= JSProto_LIMIT);
        return getSlot(APPLICATION_SLOTS + JSProto_LIMIT + key);
    }

    void setPrototype(JSProtoKey key, const Value& value) {
        MOZ_ASSERT(key <= JSProto_LIMIT);
        setSlot(APPLICATION_SLOTS + JSProto_LIMIT + key, value);
    }

    bool classIsInitialized(JSProtoKey key) const {
        bool inited = !getConstructor(key).isUndefined();
        MOZ_ASSERT(inited == !getPrototype(key).isUndefined());
        return inited;
    }

    bool functionObjectClassesInitialized() const {
        bool inited = classIsInitialized(JSProto_Function);
        MOZ_ASSERT(inited == classIsInitialized(JSProto_Object));
        return inited;
    }

    /*
     * Lazy standard classes need a way to indicate they have been initialized.
     * Otherwise, when we delete them, we might accidentally recreate them via
     * a lazy initialization. We use the presence of an object in the
     * getConstructor(key) reserved slot to indicate that they've been
     * initialized.
     *
     * Note: A few builtin objects, like JSON and Math, are not constructors,
     * so getConstructor is a bit of a misnomer.
     */
    bool isStandardClassResolved(JSProtoKey key) const {
        // If the constructor is undefined, then it hasn't been initialized.
        MOZ_ASSERT(getConstructor(key).isUndefined() ||
                   getConstructor(key).isObject());
        return !getConstructor(key).isUndefined();
    }

    /*
     * Using a Handle<GlobalObject*> as a Handle<Object*> is always safe as
     * GlobalObject derives JSObject. However, with C++'s semantics, Handle<T>
     * is not related to Handle<S>, independent of how S and T are related.
     * Further, Handle stores an indirect pointer and, again because of C++'s
     * semantics, T** is not related to S**, independent of how S and T are
     * related. Since we know that this specific case is safe, we provide a
     * manual upcast operation here to do the reinterpret_cast in a known-safe
     * manner.
     */
    static HandleObject upcast(Handle<GlobalObject*> global) {
        return HandleObject::fromMarkedLocation(
                reinterpret_cast<JSObject * const*>(global.address()));
    }

  private:
    bool arrayClassInitialized() const {
        return classIsInitialized(JSProto_Array);
    }

    bool booleanClassInitialized() const {
        return classIsInitialized(JSProto_Boolean);
    }
    bool numberClassInitialized() const {
        return classIsInitialized(JSProto_Number);
    }
    bool stringClassInitialized() const {
        return classIsInitialized(JSProto_String);
    }
    bool regexpClassInitialized() const {
        return classIsInitialized(JSProto_RegExp);
    }
    bool arrayBufferClassInitialized() const {
        return classIsInitialized(JSProto_ArrayBuffer);
    }
    bool sharedArrayBufferClassInitialized() const {
        return classIsInitialized(JSProto_SharedArrayBuffer);
    }
    bool errorClassesInitialized() const {
        return classIsInitialized(JSProto_Error);
    }
    bool dataViewClassInitialized() const {
        return classIsInitialized(JSProto_DataView);
    }

    // Disallow use of unqualified JSObject::create in GlobalObject.
    static GlobalObject* create(...) = delete;

    friend struct ::JSRuntime;
    static GlobalObject* createInternal(JSContext* cx, const Class* clasp);

  public:
    static GlobalObject*
    new_(JSContext* cx, const Class* clasp, JSPrincipals* principals,
         JS::OnNewGlobalHookOption hookOption, const JS::CompartmentOptions& options);

    /*
     * Create a constructor function with the specified name and length using
     * ctor, a method which creates objects with the given class.
     */
    static JSFunction*
    createConstructor(JSContext* cx,  JSNative ctor, JSAtom* name, unsigned length,
                      gc::AllocKind kind = gc::AllocKind::FUNCTION,
                      const JSJitInfo* jitInfo = nullptr);

    /*
     * Create an object to serve as [[Prototype]] for instances of the given
     * class, using |Object.prototype| as its [[Prototype]].  Users creating
     * prototype objects with particular internal structure (e.g. reserved
     * slots guaranteed to contain values of particular types) must immediately
     * complete the minimal initialization to make the returned object safe to
     * touch.
     */
    static NativeObject*
    createBlankPrototype(JSContext* cx, Handle<GlobalObject*> global, const js::Class* clasp);

    /*
     * Identical to createBlankPrototype, but uses proto as the [[Prototype]]
     * of the returned blank prototype.
     */
    static NativeObject*
    createBlankPrototypeInheriting(JSContext* cx, Handle<GlobalObject*> global,
                                   const js::Class* clasp, HandleObject proto);

    template <typename T>
    static T*
    createBlankPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        NativeObject* res = createBlankPrototype(cx, global, &T::class_);
        return res ? &res->template as<T>() : nullptr;
    }

    static NativeObject*
    getOrCreateObjectPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (global->functionObjectClassesInitialized())
            return &global->getPrototype(JSProto_Object).toObject().as<NativeObject>();
        if (!ensureConstructor(cx, global, JSProto_Object))
            return nullptr;
        return &global->getPrototype(JSProto_Object).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateFunctionPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (global->functionObjectClassesInitialized())
            return &global->getPrototype(JSProto_Function).toObject().as<NativeObject>();
        if (!ensureConstructor(cx, global, JSProto_Object))
            return nullptr;
        return &global->getPrototype(JSProto_Function).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateArrayPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Array))
            return nullptr;
        return &global->getPrototype(JSProto_Array).toObject().as<NativeObject>();
    }

    NativeObject* maybeGetArrayPrototype() {
        if (arrayClassInitialized())
            return &getPrototype(JSProto_Array).toObject().as<NativeObject>();
        return nullptr;
    }

    static NativeObject*
    getOrCreateBooleanPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Boolean))
            return nullptr;
        return &global->getPrototype(JSProto_Boolean).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateNumberPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Number))
            return nullptr;
        return &global->getPrototype(JSProto_Number).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateStringPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_String))
            return nullptr;
        return &global->getPrototype(JSProto_String).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateSymbolPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Symbol))
            return nullptr;
        return &global->getPrototype(JSProto_Symbol).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreatePromisePrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Promise))
            return nullptr;
        return &global->getPrototype(JSProto_Promise).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateRegExpPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_RegExp))
            return nullptr;
        return &global->getPrototype(JSProto_RegExp).toObject().as<NativeObject>();
    }

    JSObject* maybeGetRegExpPrototype() {
        if (regexpClassInitialized())
            return &getPrototype(JSProto_RegExp).toObject();
        return nullptr;
    }

    static NativeObject*
    getOrCreateSavedFramePrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_SavedFrame))
            return nullptr;
        return &global->getPrototype(JSProto_SavedFrame).toObject().as<NativeObject>();
    }

    static JSObject*
    getOrCreateArrayBufferPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_ArrayBuffer))
            return nullptr;
        return &global->getPrototype(JSProto_ArrayBuffer).toObject();
    }

    static JSObject*
    getOrCreateSharedArrayBufferPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_SharedArrayBuffer))
            return nullptr;
        return &global->getPrototype(JSProto_SharedArrayBuffer).toObject();
    }

    static JSObject*
    getOrCreateCustomErrorPrototype(JSContext* cx, Handle<GlobalObject*> global,
                                    JSExnType exnType)
    {
        JSProtoKey key = GetExceptionProtoKey(exnType);
        if (!ensureConstructor(cx, global, key))
            return nullptr;
        return &global->getPrototype(key).toObject();
    }

    static JSFunction*
    getOrCreateErrorConstructor(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Error))
            return nullptr;
        return &global->getConstructor(JSProto_Error).toObject().as<JSFunction>();
    }

    static JSObject*
    getOrCreateErrorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateCustomErrorPrototype(cx, global, JSEXN_ERR);
    }

    static NativeObject*
    getOrCreateSetPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Set))
            return nullptr;
        return &global->getPrototype(JSProto_Set).toObject().as<NativeObject>();
    }

    static NativeObject*
    getOrCreateWeakSetPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_WeakSet))
            return nullptr;
        return &global->getPrototype(JSProto_WeakSet).toObject().as<NativeObject>();
    }

    static JSObject*
    getOrCreateIntlObject(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, APPLICATION_SLOTS + JSProto_Intl, initIntlObject);
    }

    static JSObject*
    getOrCreateTypedObjectModule(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, APPLICATION_SLOTS + JSProto_TypedObject,
                                 initTypedObjectModule);
    }

    static JSObject*
    getOrCreateSimdGlobalObject(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, APPLICATION_SLOTS + JSProto_SIMD, initSimdObject);
    }

    // Get the type descriptor for one of the SIMD types.
    // simdType is one of the JS_SIMDTYPEREPR_* constants.
    // Implemented in builtin/SIMD.cpp.
    static SimdTypeDescr*
    getOrCreateSimdTypeDescr(JSContext* cx, Handle<GlobalObject*> global, SimdType simdType);

    TypedObjectModuleObject& getTypedObjectModule() const;

    JSObject* getLegacyIteratorPrototype() {
        return &getPrototype(JSProto_Iterator).toObject();
    }

    static JSObject*
    getOrCreateCollatorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, COLLATOR_PROTO, initIntlObject);
    }

    static JSFunction*
    getOrCreateNumberFormatConstructor(JSContext* cx, Handle<GlobalObject*> global) {
        JSObject* obj = getOrCreateObject(cx, global, NUMBER_FORMAT, initIntlObject);
        return obj ? &obj->as<JSFunction>() : nullptr;
    }

    static JSObject*
    getOrCreateNumberFormatPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, NUMBER_FORMAT_PROTO, initIntlObject);
    }

    static JSFunction*
    getOrCreateDateTimeFormatConstructor(JSContext* cx, Handle<GlobalObject*> global) {
        JSObject* obj = getOrCreateObject(cx, global, DATE_TIME_FORMAT, initIntlObject);
        return obj ? &obj->as<JSFunction>() : nullptr;
    }

    static JSObject*
    getOrCreateDateTimeFormatPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, DATE_TIME_FORMAT_PROTO, initIntlObject);
    }

    static JSObject*
    getOrCreatePluralRulesPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, PLURAL_RULES_PROTO, initIntlObject);
    }

    static JSObject*
    getOrCreateRelativeTimeFormatPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, RELATIVE_TIME_FORMAT_PROTO, initIntlObject);
    }

    static bool ensureModulePrototypesCreated(JSContext *cx, Handle<GlobalObject*> global);

    JSObject* maybeGetModulePrototype() {
        Value value = getSlot(MODULE_PROTO);
        return value.isUndefined() ? nullptr : &value.toObject();
    }

    JSObject* maybeGetImportEntryPrototype() {
        Value value = getSlot(IMPORT_ENTRY_PROTO);
        return value.isUndefined() ? nullptr : &value.toObject();
    }

    JSObject* maybeGetExportEntryPrototype() {
        Value value = getSlot(EXPORT_ENTRY_PROTO);
        return value.isUndefined() ? nullptr : &value.toObject();
    }

    JSObject* maybeGetRequestedModulePrototype() {
        Value value = getSlot(REQUESTED_MODULE_PROTO);
        return value.isUndefined() ? nullptr : &value.toObject();
    }

    JSObject* getModulePrototype() {
        JSObject* proto = maybeGetModulePrototype();
        MOZ_ASSERT(proto);
        return proto;
    }

    JSObject* getImportEntryPrototype() {
        JSObject* proto = maybeGetImportEntryPrototype();
        MOZ_ASSERT(proto);
        return proto;
    }

    JSObject* getExportEntryPrototype() {
        JSObject* proto = maybeGetExportEntryPrototype();
        MOZ_ASSERT(proto);
        return proto;
    }

    JSObject* getRequestedModulePrototype() {
        JSObject* proto = maybeGetRequestedModulePrototype();
        MOZ_ASSERT(proto);
        return proto;
    }

    static JSFunction*
    getOrCreateTypedArrayConstructor(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_TypedArray))
            return nullptr;
        return &global->getConstructor(JSProto_TypedArray).toObject().as<JSFunction>();
    }

    static JSObject*
    getOrCreateTypedArrayPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_TypedArray))
            return nullptr;
        return &global->getPrototype(JSProto_TypedArray).toObject();
    }

  private:
    typedef bool (*ObjectInitOp)(JSContext* cx, Handle<GlobalObject*> global);

    static JSObject*
    getOrCreateObject(JSContext* cx, Handle<GlobalObject*> global, unsigned slot,
                      ObjectInitOp init)
    {
        Value v = global->getSlotRef(slot);
        if (v.isObject())
            return &v.toObject();
        if (!init(cx, global))
            return nullptr;
        return &global->getSlot(slot).toObject();
    }

  public:
    static NativeObject*
    getOrCreateIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ITERATOR_PROTO, initIteratorProto));
    }

    static NativeObject*
    getOrCreateArrayIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ARRAY_ITERATOR_PROTO,
                                                   initArrayIteratorProto));
    }

    static NativeObject*
    getOrCreateStringIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, STRING_ITERATOR_PROTO,
                                                   initStringIteratorProto));
    }

    static NativeObject*
    getOrCreateRegExpStringIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, REGEXP_STRING_ITERATOR_PROTO,
                                               initRegExpStringIteratorProto));
    }

    static NativeObject*
    getOrCreateLegacyGeneratorObjectPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, LEGACY_GENERATOR_OBJECT_PROTO,
                                                   initLegacyGeneratorProto));
    }

    static NativeObject*
    getOrCreateStarGeneratorObjectPrototype(JSContext* cx, Handle<GlobalObject*> global)
    {
        return MaybeNativeObject(getOrCreateObject(cx, global, STAR_GENERATOR_OBJECT_PROTO,
                                                   initStarGenerators));
    }

    static NativeObject*
    getOrCreateStarGeneratorFunctionPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, STAR_GENERATOR_FUNCTION_PROTO,
                                                   initStarGenerators));
    }

    static JSObject*
    getOrCreateStarGeneratorFunction(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, STAR_GENERATOR_FUNCTION, initStarGenerators);
    }

    static NativeObject*
    getOrCreateAsyncFunctionPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ASYNC_FUNCTION_PROTO,
                                                   initAsyncFunction));
    }

    static JSObject*
    getOrCreateAsyncFunction(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, ASYNC_FUNCTION, initAsyncFunction);
    }

    static NativeObject*
    getOrCreateAsyncIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global)
    {
        return MaybeNativeObject(getOrCreateObject(cx, global, ASYNC_ITERATOR_PROTO,
                                                   initAsyncGenerators));
    }

    static NativeObject*
    getOrCreateAsyncFromSyncIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ASYNC_FROM_SYNC_ITERATOR_PROTO,
                                                   initAsyncGenerators));
    }

    static NativeObject*
    getOrCreateAsyncGenerator(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ASYNC_GENERATOR,
                                                   initAsyncGenerators));
    }

    static JSObject*
    getOrCreateAsyncGeneratorFunction(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, ASYNC_GENERATOR_FUNCTION, initAsyncGenerators);
    }

    static NativeObject*
    getOrCreateAsyncGeneratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return MaybeNativeObject(getOrCreateObject(cx, global, ASYNC_GENERATOR_PROTO,
                                                   initAsyncGenerators));
    }

    static JSObject*
    getOrCreateMapIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, MAP_ITERATOR_PROTO, initMapIteratorProto);
    }

    static JSObject*
    getOrCreateSetIteratorPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        return getOrCreateObject(cx, global, SET_ITERATOR_PROTO, initSetIteratorProto);
    }

    static JSObject*
    getOrCreateDataViewPrototype(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_DataView))
            return nullptr;
        return &global->getPrototype(JSProto_DataView).toObject();
    }

    static JSFunction*
    getOrCreatePromiseConstructor(JSContext* cx, Handle<GlobalObject*> global) {
        if (!ensureConstructor(cx, global, JSProto_Promise))
            return nullptr;
        return &global->getConstructor(JSProto_Promise).toObject().as<JSFunction>();
    }

    static NativeObject* getIntrinsicsHolder(JSContext* cx, Handle<GlobalObject*> global);

    bool maybeExistingIntrinsicValue(PropertyName* name, Value* vp) {
        Value slot = getReservedSlot(INTRINSICS);
        // If we're in the self-hosting compartment itself, the
        // intrinsics-holder isn't initialized at this point.
        if (slot.isUndefined()) {
            *vp = UndefinedValue();
            return false;
        }

        NativeObject* holder = &slot.toObject().as<NativeObject>();
        Shape* shape = holder->lookupPure(name);
        if (!shape) {
            *vp = UndefinedValue();
            return false;
        }

        *vp = holder->getSlot(shape->slot());
        return true;
    }

    Value existingIntrinsicValue(PropertyName* name) {
        Value val;
        mozilla::DebugOnly<bool> exists = maybeExistingIntrinsicValue(name, &val);
        MOZ_ASSERT(exists, "intrinsic must already have been added to holder");

        return val;
    }

    static bool
    maybeGetIntrinsicValue(JSContext* cx, Handle<GlobalObject*> global, Handle<PropertyName*> name,
                           MutableHandleValue vp, bool* exists)
    {
        NativeObject* holder = getIntrinsicsHolder(cx, global);
        if (!holder)
            return false;

        if (Shape* shape = holder->lookupPure(name)) {
            vp.set(holder->getSlot(shape->slot()));
            *exists = true;
        } else {
            *exists = false;
        }

        return true;
    }

    static bool
    getIntrinsicValue(JSContext* cx, Handle<GlobalObject*> global,
                      HandlePropertyName name, MutableHandleValue value)
    {
        bool exists = false;
        if (!GlobalObject::maybeGetIntrinsicValue(cx, global, name, value, &exists))
            return false;
        if (exists)
            return true;
        if (!cx->runtime()->cloneSelfHostedValue(cx, name, value))
            return false;
        return GlobalObject::addIntrinsicValue(cx, global, name, value);
    }

    static bool addIntrinsicValue(JSContext* cx, Handle<GlobalObject*> global,
                                  HandlePropertyName name, HandleValue value);

    static bool setIntrinsicValue(JSContext* cx, Handle<GlobalObject*> global,
                                  HandlePropertyName name, HandleValue value)
    {
        MOZ_ASSERT(cx->runtime()->isSelfHostingGlobal(global));
        RootedObject holder(cx, GlobalObject::getIntrinsicsHolder(cx, global));
        if (!holder)
            return false;
        return SetProperty(cx, holder, name, value);
    }

    static bool getSelfHostedFunction(JSContext* cx, Handle<GlobalObject*> global,
                                      HandlePropertyName selfHostedName, HandleAtom name,
                                      unsigned nargs, MutableHandleValue funVal);

    bool hasRegExpStatics() const;
    static RegExpStatics* getRegExpStatics(JSContext* cx,
                                           Handle<GlobalObject*> global);
    RegExpStatics* getAlreadyCreatedRegExpStatics() const;

    JSObject* getThrowTypeError() const {
        const Value v = getReservedSlot(THROWTYPEERROR);
        MOZ_ASSERT(v.isObject(),
                   "attempting to access [[ThrowTypeError]] too early");
        return &v.toObject();
    }

    static bool isRuntimeCodeGenEnabled(JSContext* cx, Handle<GlobalObject*> global);

    static bool getOrCreateEval(JSContext* cx, Handle<GlobalObject*> global,
                                MutableHandleObject eval);

    // Infallibly test whether the given value is the eval function for this global.
    bool valueIsEval(const Value& val);

    // Implemented in jsiter.cpp.
    static bool initIteratorProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initArrayIteratorProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initStringIteratorProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initRegExpStringIteratorProto(JSContext* cx, Handle<GlobalObject*> global);

    // Implemented in vm/GeneratorObject.cpp.
    static bool initLegacyGeneratorProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initStarGenerators(JSContext* cx, Handle<GlobalObject*> global);

    static bool initAsyncFunction(JSContext* cx, Handle<GlobalObject*> global);

    static bool initAsyncGenerators(JSContext* cx, Handle<GlobalObject*> global);

    // Implemented in builtin/MapObject.cpp.
    static bool initMapIteratorProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initSetIteratorProto(JSContext* cx, Handle<GlobalObject*> global);

    // Implemented in Intl.cpp.
    static bool initIntlObject(JSContext* cx, Handle<GlobalObject*> global);
    static bool addRelativeTimeFormatConstructor(JSContext* cx, HandleObject intl);

    // Implemented in builtin/ModuleObject.cpp
    static bool initModuleProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initImportEntryProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initExportEntryProto(JSContext* cx, Handle<GlobalObject*> global);
    static bool initRequestedModuleProto(JSContext* cx, Handle<GlobalObject*> global);

    // Implemented in builtin/TypedObject.cpp
    static bool initTypedObjectModule(JSContext* cx, Handle<GlobalObject*> global);

    // Implemented in builtin/SIMD.cpp
    static bool initSimdObject(JSContext* cx, Handle<GlobalObject*> global);
    static bool initSimdType(JSContext* cx, Handle<GlobalObject*> global, SimdType simdType);

    static bool initStandardClasses(JSContext* cx, Handle<GlobalObject*> global);
    static bool initSelfHostingBuiltins(JSContext* cx, Handle<GlobalObject*> global,
                                        const JSFunctionSpec* builtins);

    typedef js::Vector<js::ReadBarriered<js::Debugger*>, 0, js::SystemAllocPolicy> DebuggerVector;

    /*
     * The collection of Debugger objects debugging this global. If this global
     * is not a debuggee, this returns either nullptr or an empty vector.
     */
    DebuggerVector* getDebuggers() const;

    /*
     * The same, but create the empty vector if one does not already
     * exist. Returns nullptr only on OOM.
     */
    static DebuggerVector* getOrCreateDebuggers(JSContext* cx, Handle<GlobalObject*> global);

    inline NativeObject* getForOfPICObject() {
        Value forOfPIC = getReservedSlot(FOR_OF_PIC_CHAIN);
        if (forOfPIC.isUndefined())
            return nullptr;
        return &forOfPIC.toObject().as<NativeObject>();
    }
    static NativeObject* getOrCreateForOfPICObject(JSContext* cx, Handle<GlobalObject*> global);

    JSObject* windowProxy() const {
        return &getReservedSlot(WINDOW_PROXY).toObject();
    }
    JSObject* maybeWindowProxy() const {
        Value v = getReservedSlot(WINDOW_PROXY);
        MOZ_ASSERT(v.isObject() || v.isUndefined());
        return v.isObject() ? &v.toObject() : nullptr;
    }
    void setWindowProxy(JSObject* windowProxy) {
        setReservedSlot(WINDOW_PROXY, ObjectValue(*windowProxy));
    }

    // Returns either this global's star-generator function prototype, or null
    // if that object was never created.  Dodgy; for use only in also-dodgy
    // GlobalHelperThreadState::mergeParseTaskCompartment().
    JSObject* getStarGeneratorFunctionPrototype();
};

/*
 * Unless otherwise specified, define ctor.prototype = proto as non-enumerable,
 * non-configurable, and non-writable; and define proto.constructor = ctor as
 * non-enumerable but configurable and writable.
 */
extern bool
LinkConstructorAndPrototype(JSContext* cx, JSObject* ctor, JSObject* proto,
                            unsigned prototypeAttrs = JSPROP_PERMANENT | JSPROP_READONLY,
                            unsigned constructorAttrs = 0);

/*
 * Define properties and/or functions on any object. Either ps or fs, or both,
 * may be null.
 */
extern bool
DefinePropertiesAndFunctions(JSContext* cx, HandleObject obj,
                             const JSPropertySpec* ps, const JSFunctionSpec* fs);

typedef HashSet<GlobalObject*, DefaultHasher<GlobalObject*>, SystemAllocPolicy> GlobalObjectSet;

extern bool
DefineToStringTag(JSContext *cx, HandleObject obj, JSAtom* tag);

/*
 * Convenience templates to generic constructor and prototype creation functions
 * for ClassSpecs.
 */

template<JSNative ctor, unsigned length, gc::AllocKind kind, const JSJitInfo* jitInfo = nullptr>
JSObject*
GenericCreateConstructor(JSContext* cx, JSProtoKey key)
{
    // Note - We duplicate the trick from ClassName() so that we don't need to
    // include jsatominlines.h here.
    PropertyName* name = (&cx->names().Null)[key];
    return GlobalObject::createConstructor(cx, ctor, name, length, kind, jitInfo);
}

inline JSObject*
GenericCreatePrototype(JSContext* cx, JSProtoKey key)
{
    MOZ_ASSERT(key != JSProto_Object);
    const Class* clasp = ProtoKeyToClass(key);
    MOZ_ASSERT(clasp);
    JSProtoKey protoKey = InheritanceProtoKeyForStandardClass(key);
    if (!GlobalObject::ensureConstructor(cx, cx->global(), protoKey))
        return nullptr;
    RootedObject parentProto(cx, &cx->global()->getPrototype(protoKey).toObject());
    return GlobalObject::createBlankPrototypeInheriting(cx, cx->global(), clasp, parentProto);
}

inline JSProtoKey
StandardProtoKeyOrNull(const JSObject* obj)
{
    return JSCLASS_CACHED_PROTO_KEY(obj->getClass());
}

JSObject*
NewSingletonObjectWithFunctionPrototype(JSContext* cx, Handle<GlobalObject*> global);

} // namespace js

template<>
inline bool
JSObject::is<js::GlobalObject>() const
{
    return !!(getClass()->flags & JSCLASS_IS_GLOBAL);
}

#endif /* vm_GlobalObject_h */
