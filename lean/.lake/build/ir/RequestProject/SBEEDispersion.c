// Lean compiler output
// Module: RequestProject.SBEEDispersion
// Imports: public import Init public import Mathlib public import RequestProject.BlockCRTEnergy
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
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_castEmbedding___at___00Int_divisorsAntidiag_spec__0___lam__0(lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_map___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Nat_decidablePrime_x27(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Function_Embedding_trans___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lp_mathlib_Nat_decidablePrime_x27(x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_nat_to_int(x_1);
x_8 = lean_nat_to_int(x_5);
x_9 = lean_int_mul(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_10 = lean_int_sub(x_9, x_2);
lean_dec(x_9);
x_11 = l_Int_decidableDvd(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_mathlib_Nat_castEmbedding___at___00Int_divisorsAntidiag_spec__0___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0;
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(lp_mathlib_Function_Embedding_trans___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1;
x_7 = lean_int_add(x_2, x_6);
x_8 = lean_int_sub(x_7, x_1);
lean_dec(x_1);
lean_dec(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_List_range(x_9);
x_11 = lp_mathlib_Finset_map___redArg(x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_alloc_closure((void*)(lp_RequestProject_SBEEDispersion_lemmaD__set___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_nat_to_int(x_3);
x_7 = lean_int_neg(x_6);
x_8 = lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0(x_7, x_6);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_mul(x_9, x_1);
x_11 = lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(x_1, x_10);
lean_dec(x_10);
x_12 = lp_mathlib_Multiset_product___redArg(x_8, x_11);
x_13 = lp_mathlib_Multiset_filter___redArg(x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_SBEEDispersion_lemmaD__set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_SBEEDispersion_lemmaD__set(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_RequestProject_addLeftEmbedding___at___00Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_BlockCRTEnergy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SBEEDispersion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_BlockCRTEnergy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0 = _init_lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0();
lean_mark_persistent(lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__0);
lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1 = _init_lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1();
lean_mark_persistent(lp_RequestProject_Finset_Icc___at___00SBEEDispersion_lemmaD__set_spec__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
