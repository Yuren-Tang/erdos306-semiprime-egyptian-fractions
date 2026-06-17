// Lean compiler output
// Module: RequestProject.R2AssemblySkeleton
// Imports: public import Init public import RequestProject.BlockMassPool public import RequestProject.ExtraEnergyMinorArc public import RequestProject.ExtraMinorDamping public import RequestProject.ArcConstructionSigma
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
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lp_RequestProject_CircleMethod_ctrlEdges(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CircleMethod_gadgetEdges___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2Edges(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges___lam__0(lean_object*);
uint8_t lp_mathlib_List_elem___at___00__private_Mathlib_Tactic_Translate_Core_0__Mathlib_Tactic_Translate_applyReplacementFun_visitApp_spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_nat_mul(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_CircleMethod_gadgetEdges___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_CircleMethod_gadgetEdges___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_gadgetEdges___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_gadgetEdges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_RequestProject_CircleMethod_gadgetEdges___closed__0;
x_4 = lp_mathlib_Multiset_product___redArg(x_1, x_2);
x_5 = lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lp_mathlib_List_elem___at___00__private_Mathlib_Tactic_Translate_Core_0__Mathlib_Tactic_Translate_applyReplacementFun_visitApp_spec__4(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_7;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_8);
x_2 = x_7;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = 0;
x_9 = lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0_spec__1(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2Edges(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lp_RequestProject_CircleMethod_ctrlEdges(x_1);
x_6 = lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(x_2, x_5);
x_7 = lp_RequestProject_CircleMethod_gadgetEdges(x_3, x_4);
x_8 = lp_RequestProject_List_foldrTR___at___00Multiset_ndunion___at___00CircleMethod_r2Edges_spec__0_spec__0(x_7, x_6);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_BlockMassPool(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ExtraEnergyMinorArc(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ExtraMinorDamping(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ArcConstructionSigma(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2AssemblySkeleton(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_BlockMassPool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ExtraEnergyMinorArc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ExtraMinorDamping(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ArcConstructionSigma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CircleMethod_gadgetEdges___closed__0 = _init_lp_RequestProject_CircleMethod_gadgetEdges___closed__0();
lean_mark_persistent(lp_RequestProject_CircleMethod_gadgetEdges___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
