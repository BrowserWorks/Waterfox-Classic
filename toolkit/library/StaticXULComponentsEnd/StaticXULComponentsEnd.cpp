#include "mozilla/Module.h"

/* Ensure end_kPStaticModules is at the end of the .kPStaticModules section
 * on Windows. Somehow, placing the object last is not enough with PGO/LTCG. */
#ifdef _MSC_VER
/* Sections on Windows are in two parts, separated with $. When linking,
 * sections with the same first part are all grouped, and ordered
 * alphabetically with the second part as sort key. */
#  pragma section(".kPStaticModules$Z", read)
#  undef NSMODULE_SECTION
#  define NSMODULE_SECTION __declspec(allocate(".kPStaticModules$Z"), dllexport)
#elif MOZ_LTO
/* Clang+lld with LTO does not order modules correctly either, but fortunately
 * the same trick works. */
#  undef NSMODULE_SECTION
#  define NSMODULE_SECTION __attribute__((section(".kPStaticModules$Z"), visibility("default")))
#endif
NSMODULE_DEFN(end_kPStaticModules) = nullptr;
