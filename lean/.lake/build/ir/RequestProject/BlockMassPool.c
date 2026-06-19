// Lean compiler output
// Module: RequestProject.BlockMassPool
// Imports: public import Init public import RequestProject.DyadicPrimes
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
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockPrimes(lean_object*);
static lean_object* lp_RequestProject_CircleMethod_blockPrimes___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_bind___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_GlobalControl_dyadicBlock___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockPrimes___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lp_mathlib_Multiset_bind___redArg(x_1, x_3);
x_5 = lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(x_4);
return x_5;
}
}
static lean_object* _init_lp_RequestProject_CircleMethod_blockPrimes___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_GlobalControl_dyadicBlock___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockPrimes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mul(x_2, x_1);
x_4 = lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(x_1, x_3);
lean_dec(x_3);
x_5 = lp_RequestProject_CircleMethod_blockPrimes___closed__0;
x_6 = lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockPrimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_CircleMethod_blockPrimes(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_Finset_biUnion___at___00CircleMethod_blockPrimes_spec__0___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_DyadicPrimes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_BlockMassPool(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_DyadicPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CircleMethod_blockPrimes___closed__0 = _init_lp_RequestProject_CircleMethod_blockPrimes___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_blockPrimes___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
