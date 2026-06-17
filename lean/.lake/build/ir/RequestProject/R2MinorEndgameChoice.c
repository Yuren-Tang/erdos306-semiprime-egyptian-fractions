// Lean compiler output
// Module: RequestProject.R2MinorEndgameChoice
// Imports: public import Init public import RequestProject.R2MinorReadyArc public import RequestProject.R2ExtraGadgetChoice
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
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_CircleMethod_r2__extraMinorGadgetMemData__of__choiceData___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lp_RequestProject_CircleMethod_r2__extraMinorGadgetMemData__of__choiceData___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___redArg(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_CircleMethod_r2__minorEndgameGadgetLanes__of__choiceLanes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2MinorReadyArc(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_R2ExtraGadgetChoice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_R2MinorEndgameChoice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2MinorReadyArc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_R2ExtraGadgetChoice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
