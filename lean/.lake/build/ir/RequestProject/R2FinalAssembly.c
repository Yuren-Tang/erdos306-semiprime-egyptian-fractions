// Lean compiler output
// Module: RequestProject.R2FinalAssembly
// Imports: public import Init public import RequestProject.R2AssemblyFields public import RequestProject.R2MinorCover public import RequestProject.R2NumericFields
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
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg___boxed(lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_11 = lp_RequestProject_CircleMethod_R2ConcreteData_E___redArg(x_4);
x_12 = lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(x_1, x_4);
x_13 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_6);
lean_ctor_set(x_13, 4, x_8);
lean_ctor_set(x_13, 5, x_9);
lean_ctor_set(x_13, 6, x_10);
lean_ctor_set(x_13, 7, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_CircleMethod_R2FinalSupply_toArcConstruction(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2AssemblyFields(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2MinorCover(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2NumericFields(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2FinalAssembly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2AssemblyFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2MinorCover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2NumericFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
