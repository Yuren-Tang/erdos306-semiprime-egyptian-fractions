// Lean compiler output
// Module: RequestProject.R2ExtraMultiGadget
// Imports: public import Init public import RequestProject.R2FourierFactor
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
lean_object* lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_multiGadgetEdges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_multiGadgetEdges___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lp_RequestProject_Finset_image___at___00CircleMethod_ctrlEdges_spec__0___redArg(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2FourierFactor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2ExtraMultiGadget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2FourierFactor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
