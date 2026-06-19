// Lean compiler output
// Module: RequestProject.ArcConstruction
// Imports: public import Init public import RequestProject.CircleMethodArcs public import RequestProject.CircleMethodMainTerm public import RequestProject.BlockSystemConstruction
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
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges___lam__0(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_CircleMethod_ctrlEdges___closed__0;
lean_object* lp_RequestProject_GlobalControl_ctrlPairs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_nat_mul(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_CircleMethod_ctrlEdges___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_1, x_2);
x_4 = lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(x_3);
return x_4;
}
}
static lean_object* _init_lp_RequestProject_CircleMethod_ctrlEdges___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_ctrlEdges___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_ctrlEdges(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_RequestProject_CircleMethod_ctrlEdges___closed__0;
x_3 = lp_RequestProject_GlobalControl_ctrlPairs(x_1);
x_4 = lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_CircleMethodArcs(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_CircleMethodMainTerm(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_BlockSystemConstruction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ArcConstruction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_CircleMethodArcs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_CircleMethodMainTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_BlockSystemConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CircleMethod_ctrlEdges___closed__0 = _init_lp_RequestProject_CircleMethod_ctrlEdges___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_ctrlEdges___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
