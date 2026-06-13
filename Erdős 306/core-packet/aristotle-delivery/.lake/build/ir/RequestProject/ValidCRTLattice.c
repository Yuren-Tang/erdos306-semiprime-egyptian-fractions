// Lean compiler output
// Module: RequestProject.ValidCRTLattice
// Imports: public import Init public import Mathlib public import RequestProject.ReciprocalCRTProduct
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
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__inCRTLattice___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__pred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_a2(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__pred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__fourSeedLineWitness___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__fourSeedLineWitness(lean_object*);
static lean_object* lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__smul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__smul(lean_object*, lean_object*);
lean_object* lp_RequestProject_a3(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__inCRTLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_a1(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__pred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set(x_13, 5, x_6);
lean_ctor_set(x_13, 6, x_7);
lean_ctor_set(x_13, 7, x_8);
lean_ctor_set(x_13, 8, x_9);
lean_ctor_set(x_13, 9, x_10);
lean_ctor_set(x_13, 10, x_11);
lean_ctor_set(x_13, 11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__pred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set(x_14, 5, x_6);
lean_ctor_set(x_14, 6, x_7);
lean_ctor_set(x_14, 7, x_8);
lean_ctor_set(x_14, 8, x_9);
lean_ctor_set(x_14, 9, x_10);
lean_ctor_set(x_14, 10, x_11);
lean_ctor_set(x_14, 11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__fourSeedLineWitness(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_ctor_get(x_1, 5);
x_7 = lean_ctor_get(x_1, 6);
x_8 = lean_ctor_get(x_1, 7);
x_9 = lean_ctor_get(x_1, 8);
x_10 = lean_ctor_get(x_1, 9);
x_11 = lp_RequestProject_a1(x_1);
x_12 = lp_RequestProject_a2(x_1);
x_13 = lp_RequestProject_a3(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_5);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_7);
lean_ctor_set(x_14, 7, x_8);
lean_ctor_set(x_14, 8, x_9);
lean_ctor_set(x_14, 9, x_11);
lean_ctor_set(x_14, 10, x_12);
lean_ctor_set(x_14, 11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__fourSeedLineWitness___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_validCRTProductHit__of__fourSeedLineWitness(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_ctor_get(x_1, 7);
x_10 = lean_ctor_get(x_1, 8);
x_11 = lean_ctor_get(x_1, 9);
x_12 = lean_ctor_get(x_1, 10);
x_13 = lean_ctor_get(x_1, 11);
x_14 = lean_int_mul(x_6, x_7);
x_15 = lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set(x_16, 5, x_6);
lean_ctor_set(x_16, 6, x_8);
lean_ctor_set(x_16, 7, x_9);
lean_ctor_set(x_16, 8, x_10);
lean_ctor_set(x_16, 9, x_7);
lean_ctor_set(x_16, 10, x_11);
lean_ctor_set(x_16, 11, x_12);
lean_ctor_set(x_16, 12, x_13);
lean_ctor_set(x_16, 13, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__inCRTLattice___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set(x_13, 5, x_6);
lean_ctor_set(x_13, 6, x_7);
lean_ctor_set(x_13, 7, x_8);
lean_ctor_set(x_13, 8, x_9);
lean_ctor_set(x_13, 9, x_10);
lean_ctor_set(x_13, 10, x_11);
lean_ctor_set(x_13, 11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__of__inCRTLattice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set(x_14, 5, x_6);
lean_ctor_set(x_14, 6, x_7);
lean_ctor_set(x_14, 7, x_8);
lean_ctor_set(x_14, 8, x_9);
lean_ctor_set(x_14, 9, x_10);
lean_ctor_set(x_14, 10, x_11);
lean_ctor_set(x_14, 11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__smul(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = lean_ctor_get(x_1, 6);
x_6 = lean_ctor_get(x_1, 7);
x_7 = lean_ctor_get(x_1, 8);
x_8 = lean_ctor_get(x_1, 9);
x_9 = lean_ctor_get(x_1, 10);
x_10 = lean_ctor_get(x_1, 11);
x_11 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_12 = lean_int_mul(x_2, x_5);
lean_dec(x_5);
x_13 = lean_int_mul(x_2, x_6);
lean_dec(x_6);
x_14 = lean_int_mul(x_2, x_7);
lean_dec(x_7);
x_15 = lean_int_mul(x_2, x_8);
lean_dec(x_8);
x_16 = lean_int_mul(x_2, x_9);
lean_dec(x_9);
x_17 = lean_int_mul(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_1, 11, x_17);
lean_ctor_set(x_1, 10, x_16);
lean_ctor_set(x_1, 9, x_15);
lean_ctor_set(x_1, 8, x_14);
lean_ctor_set(x_1, 7, x_13);
lean_ctor_set(x_1, 6, x_12);
lean_ctor_set(x_1, 5, x_11);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
x_24 = lean_ctor_get(x_1, 6);
x_25 = lean_ctor_get(x_1, 7);
x_26 = lean_ctor_get(x_1, 8);
x_27 = lean_ctor_get(x_1, 9);
x_28 = lean_ctor_get(x_1, 10);
x_29 = lean_ctor_get(x_1, 11);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_30 = lean_int_mul(x_2, x_23);
lean_dec(x_23);
x_31 = lean_int_mul(x_2, x_24);
lean_dec(x_24);
x_32 = lean_int_mul(x_2, x_25);
lean_dec(x_25);
x_33 = lean_int_mul(x_2, x_26);
lean_dec(x_26);
x_34 = lean_int_mul(x_2, x_27);
lean_dec(x_27);
x_35 = lean_int_mul(x_2, x_28);
lean_dec(x_28);
x_36 = lean_int_mul(x_2, x_29);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_37, 2, x_20);
lean_ctor_set(x_37, 3, x_21);
lean_ctor_set(x_37, 4, x_22);
lean_ctor_set(x_37, 5, x_30);
lean_ctor_set(x_37, 6, x_31);
lean_ctor_set(x_37, 7, x_32);
lean_ctor_set(x_37, 8, x_33);
lean_ctor_set(x_37, 9, x_34);
lean_ctor_set(x_37, 10, x_35);
lean_ctor_set(x_37, 11, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_validCRTProductHit__smul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_validCRTProductHit__smul(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ReciprocalCRTProduct(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ValidCRTLattice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ReciprocalCRTProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0 = _init_lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0();
lean_mark_persistent(lp_RequestProject_fourSeedLineWitness__of__validCRTProductHit___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
