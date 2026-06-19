// Lean compiler output
// Module: RequestProject.R2MassBatchCandidatePool
// Imports: public import Init public import RequestProject.R2MassBatchPoolSupply
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
lean_object* lp_RequestProject_CircleMethod_ctrlEdges(lean_object*);
lean_object* lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_gadgetEdges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden(lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0;
lean_object* lp_mathlib_List_offDiag___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_List_diff___at___00Multiset_sub___at___00CircleMethod_Wcount_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lp_RequestProject_Multiset_filter___at___00Finset_filter___at___00GlobalControl_internalPairs_spec__0_spec__0___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0(lean_object*);
lean_object* lp_RequestProject_GlobalControl_blockSupport(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_nat_mul(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_blockSupportPairPool___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_blockSupportPairPool(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0;
x_3 = lp_RequestProject_GlobalControl_blockSupport(x_1);
x_4 = lp_mathlib_List_offDiag___redArg(x_3);
x_5 = lp_RequestProject_Multiset_filter___at___00Finset_filter___at___00GlobalControl_internalPairs_spec__0_spec__0___redArg(x_4);
x_6 = lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lp_RequestProject_CircleMethod_ctrlEdges(x_3);
x_7 = lp_RequestProject_CircleMethod_gadgetEdges(x_4, x_5);
x_8 = lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(x_7, x_6);
x_9 = lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_residualForbidden___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualForbidden___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_residualForbidden(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lp_RequestProject_CircleMethod_blockSupportPairPool(x_3);
x_5 = lp_RequestProject_CircleMethod_residualForbidden___redArg(x_1, x_2);
x_6 = lp_RequestProject_List_diff___at___00Multiset_sub___at___00CircleMethod_Wcount_spec__1_spec__2(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_residualPairPool___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_residualPairPool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_residualPairPool(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2MassBatchPoolSupply(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2MassBatchCandidatePool(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2MassBatchPoolSupply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0 = _init_lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_blockSupportPairPool___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
