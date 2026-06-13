// Lean compiler output
// Module: RequestProject.ReciprocalCRTProduct
// Imports: public import Init public import Mathlib public import RequestProject.ClusterLineIncidence public import RequestProject.CRTLatticeCore
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
LEAN_EXPORT lean_object* lp_RequestProject_a2(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a2___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a1___boxed(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a3(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a1(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a3___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_a1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 10);
x_3 = lean_ctor_get(x_1, 13);
x_4 = lean_int_sub(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_a1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_a1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_a2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 11);
x_3 = lean_ctor_get(x_1, 13);
x_4 = lean_int_sub(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_a2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_a2(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_a3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 12);
x_3 = lean_ctor_get(x_1, 13);
x_4 = lean_int_sub(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_a3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_a3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ClusterLineIncidence(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_CRTLatticeCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ReciprocalCRTProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ClusterLineIncidence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_CRTLatticeCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
