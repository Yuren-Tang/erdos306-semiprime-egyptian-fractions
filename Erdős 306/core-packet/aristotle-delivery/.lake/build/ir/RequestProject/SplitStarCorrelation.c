// Lean compiler output
// Module: RequestProject.SplitStarCorrelation
// Imports: public import Init public import Mathlib public import RequestProject.ResidualPrimeShellCRT
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_splitAnchoredStar__of__anchoredCRTProductHit___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_splitAnchoredStar__of__anchoredCRTProductHit(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_splitAnchoredStar__of__anchoredCRTProductHit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_ctor_get(x_1, 7);
x_10 = lean_ctor_get(x_1, 8);
x_11 = lean_ctor_get(x_1, 9);
x_12 = lean_ctor_get(x_1, 10);
x_13 = lean_ctor_get(x_1, 11);
x_14 = lean_ctor_get(x_1, 12);
x_15 = lean_ctor_get(x_1, 13);
x_16 = lean_ctor_get(x_1, 14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc_n(x_9, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_5);
lean_ctor_set(x_17, 4, x_6);
lean_ctor_set(x_17, 5, x_7);
lean_ctor_set(x_17, 6, x_8);
lean_ctor_set(x_17, 7, x_9);
lean_ctor_set(x_17, 8, x_9);
lean_ctor_set(x_17, 9, x_13);
lean_ctor_set(x_17, 10, x_14);
lean_ctor_set(x_17, 11, x_15);
lean_ctor_set(x_17, 12, x_16);
lean_ctor_set(x_17, 13, x_10);
lean_ctor_set(x_17, 14, x_11);
lean_ctor_set(x_17, 15, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_splitAnchoredStar__of__anchoredCRTProductHit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_splitAnchoredStar__of__anchoredCRTProductHit(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_ctor_get(x_1, 7);
x_10 = lean_ctor_get(x_1, 9);
x_11 = lean_ctor_get(x_1, 10);
x_12 = lean_ctor_get(x_1, 11);
x_13 = lean_ctor_get(x_1, 12);
x_14 = lean_ctor_get(x_1, 13);
x_15 = lean_ctor_get(x_1, 14);
x_16 = lean_ctor_get(x_1, 15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_5);
lean_ctor_set(x_17, 4, x_6);
lean_ctor_set(x_17, 5, x_7);
lean_ctor_set(x_17, 6, x_8);
lean_ctor_set(x_17, 7, x_9);
lean_ctor_set(x_17, 8, x_14);
lean_ctor_set(x_17, 9, x_15);
lean_ctor_set(x_17, 10, x_16);
lean_ctor_set(x_17, 11, x_10);
lean_ctor_set(x_17, 12, x_11);
lean_ctor_set(x_17, 13, x_12);
lean_ctor_set(x_17, 14, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_anchoredCRTProductHit__of__splitAnchoredStar__diagonal(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ResidualPrimeShellCRT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SplitStarCorrelation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ResidualPrimeShellCRT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
