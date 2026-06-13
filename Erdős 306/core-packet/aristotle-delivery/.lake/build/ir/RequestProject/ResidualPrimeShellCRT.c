// Lean compiler output
// Module: RequestProject.ResidualPrimeShellCRT
// Imports: public import Init public import Mathlib public import RequestProject.AnchoredCRTLattice public import RequestProject.ValidCRTLattice public import RequestProject.ReciprocalCRTProduct public import RequestProject.PrimitiveProjectiveNormalization
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
LEAN_EXPORT lean_object* lp_RequestProject_sixVarData__of__anchored___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_sixVarData__of__anchored(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_reconstructY___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_reconstructY(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_sixVarData__of__anchored(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_ctor_get(x_1, 7);
x_4 = lean_ctor_get(x_1, 11);
x_5 = lean_ctor_get(x_1, 12);
x_6 = lean_ctor_get(x_1, 13);
x_7 = lean_ctor_get(x_1, 14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_sixVarData__of__anchored___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_sixVarData__of__anchored(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_reconstructY(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 4);
x_5 = lean_ctor_get(x_1, 5);
x_6 = lean_int_add(x_3, x_2);
x_7 = lean_int_add(x_4, x_2);
x_8 = lean_int_add(x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_reconstructY___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_reconstructY(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_AnchoredCRTLattice(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ValidCRTLattice(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ReciprocalCRTProduct(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_PrimitiveProjectiveNormalization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ResidualPrimeShellCRT(uint8_t builtin) {
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
res = initialize_RequestProject_RequestProject_ValidCRTLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ReciprocalCRTProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_PrimitiveProjectiveNormalization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
