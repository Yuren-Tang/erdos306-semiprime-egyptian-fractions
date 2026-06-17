// Lean compiler output
// Module: RequestProject.ArcConstructionExtra
// Imports: public import Init public import RequestProject.ArcConstruction public import RequestProject.FiberCount
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
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_Finset_biUnion___at___00GlobalControl_blockSupport_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_edgePrimeSupport(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_extraPrimeSupport(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0;
lean_object* lp_RequestProject_GlobalControl_blockSupport(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0(lean_object*);
static lean_object* lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0;
lean_object* lp_mathlib_Nat_primeFactors___boxed(lean_object*);
lean_object* lp_RequestProject_List_diff___at___00Multiset_sub___at___00GlobalControl_segStarts_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_mathlib_Nat_primeFactors___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_edgePrimeSupport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0;
x_3 = lp_RequestProject_Finset_biUnion___at___00GlobalControl_blockSupport_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_extraPrimeSupport(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_RequestProject_CircleMethod_edgePrimeSupport(x_2);
x_4 = lp_RequestProject_GlobalControl_blockSupport(x_1);
x_5 = lp_RequestProject_List_diff___at___00Multiset_sub___at___00GlobalControl_segStarts_spec__0_spec__0(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_primeSupportPeriod___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0;
x_4 = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(x_2, x_3);
x_5 = lean_nat_mul(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_CircleMethod_primeSupportPeriod(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ArcConstruction(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_FiberCount(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ArcConstructionExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ArcConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_FiberCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0 = _init_lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_edgePrimeSupport___closed__0);
lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0 = _init_lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_primeSupportPeriod___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
