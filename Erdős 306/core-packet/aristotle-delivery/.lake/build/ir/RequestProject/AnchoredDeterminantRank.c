// Lean compiler output
// Module: RequestProject.AnchoredDeterminantRank
// Imports: public import Init public import Mathlib public import RequestProject.AnchoredCRTLattice
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
LEAN_EXPORT lean_object* lp_RequestProject_anchoredFactorableShell__of__witness(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_detY(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_detRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_detY___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_anchoredFactorableShell__of__witness___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_detRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_detRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_int_mul(x_1, x_4);
x_6 = lean_int_mul(x_2, x_3);
x_7 = lean_int_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_detRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_detRef(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_detY(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_int_mul(x_1, x_4);
x_6 = lean_int_mul(x_2, x_3);
x_7 = lean_int_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_detY___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_detY(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredFactorableShell__of__witness(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_ctor_get(x_1, 5);
x_7 = lean_ctor_get(x_1, 6);
x_8 = lean_ctor_get(x_1, 7);
x_9 = lean_ctor_get(x_1, 8);
x_10 = lean_ctor_get(x_1, 9);
x_11 = lean_ctor_get(x_1, 10);
x_12 = lean_ctor_get(x_1, 11);
x_13 = lean_ctor_get(x_1, 12);
x_14 = lean_ctor_get(x_1, 13);
x_15 = lean_ctor_get(x_1, 14);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_5);
lean_ctor_set(x_16, 4, x_6);
lean_ctor_set(x_16, 5, x_7);
lean_ctor_set(x_16, 6, x_8);
lean_ctor_set(x_16, 7, x_9);
lean_ctor_set(x_16, 8, x_10);
lean_ctor_set(x_16, 9, x_11);
lean_ctor_set(x_16, 10, x_12);
lean_ctor_set(x_16, 11, x_13);
lean_ctor_set(x_16, 12, x_14);
lean_ctor_set(x_16, 13, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_anchoredFactorableShell__of__witness___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_anchoredFactorableShell__of__witness(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_AnchoredCRTLattice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_AnchoredDeterminantRank(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_AnchoredCRTLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
