// Lean compiler output
// Module: RequestProject.SingleBlockCounting
// Imports: public import Init public import Mathlib public import RequestProject.SBEE public import RequestProject.BlockCRTEnergy
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
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_Finset_image___at___00activeLabels_x27_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_labelClass___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_nonDominantAssignments___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels___redArg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_labelClass(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_labelClass___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_int_dec_eq(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_RequestProject_labelClass___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(lp_RequestProject_labelClass___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = lp_mathlib_Multiset_filter___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_labelClass(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_labelClass___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_labelClass___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_labelClass(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lp_RequestProject_Finset_image___at___00activeLabels_x27_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_activeLabels___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_activeLabels___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_activeLabels(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_nonDominantAssignments___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_int_dec_eq(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_RequestProject_nonDominantAssignments___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(lp_RequestProject_nonDominantAssignments___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = lp_mathlib_Multiset_filter___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_nonDominantAssignments___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_nonDominantAssignments___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_nonDominantAssignments(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SBEE(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_BlockCRTEnergy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SingleBlockCounting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SBEE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_BlockCRTEnergy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
