// Lean compiler output
// Module: RequestProject.R2ConcreteData
// Imports: public import Init public import RequestProject.R2AssemblySkeleton public import RequestProject.BlockMassPool public import RequestProject.ArcConstructionSigma public import RequestProject.CircleMethodAssembly
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
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_primeSupportPeriod(lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_r2Edges(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg___boxed(lean_object*, lean_object*);
lean_object* lp_RequestProject_GlobalControl_blockSupport(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lp_RequestProject_CircleMethod_r2Edges(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_R2ConcreteData_E___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_E___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_R2ConcreteData_E(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lp_RequestProject_GlobalControl_blockSupport(x_3);
x_5 = lp_RequestProject_CircleMethod_primeSupportPeriod(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_R2ConcreteData_L___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_R2ConcreteData_L___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_CircleMethod_R2ConcreteData_L(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2AssemblySkeleton(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_BlockMassPool(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ArcConstructionSigma(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_CircleMethodAssembly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2ConcreteData(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2AssemblySkeleton(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_BlockMassPool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ArcConstructionSigma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_CircleMethodAssembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
