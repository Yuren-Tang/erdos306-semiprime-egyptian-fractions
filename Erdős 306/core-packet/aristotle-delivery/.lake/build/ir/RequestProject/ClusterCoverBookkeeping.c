// Lean compiler output
// Module: RequestProject.ClusterCoverBookkeeping
// Imports: public import Init public import Mathlib
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
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_unionClusters(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_unionClusters___redArg(lean_object*, lean_object*);
static lean_object* lp_RequestProject_unionClusters___redArg___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_clustersContaining___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Finset_instDecidableRelSubset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_clustersContaining___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_mathlib_Finset_instDecidableRelSubset___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_RequestProject_clustersContaining___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_RequestProject_clustersContaining___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_clustersContaining(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_clustersContaining___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_lp_RequestProject_unionClusters___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_unionClusters___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_RequestProject_unionClusters___redArg___closed__0;
x_4 = lp_mathlib_Finset_biUnion___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_unionClusters(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_unionClusters___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ClusterCoverBookkeeping(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_unionClusters___redArg___closed__0 = _init_lp_RequestProject_unionClusters___redArg___closed__0();
lean_mark_persistent(lp_RequestProject_unionClusters___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
