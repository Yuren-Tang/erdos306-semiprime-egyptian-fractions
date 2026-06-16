import RequestProject.R2ConcreteData

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-!
# R2 weight selection

Once the total reciprocal load of the selected concrete edge set lies in
`[3/(2b), 3/b)`, the Bernoulli weights can be chosen uniformly.  This closes the
previously abstract `R2ConcreteData.Weights` package.
-/

/-- Uniform Bernoulli parameter tuned to make the expected reciprocal mass
exactly `1/b`. -/
def uniformTheta (D : R2ConcreteData T b) : ℕ → ℝ :=
  fun _ => (1 / (b : ℝ)) / recipLoad D.E

lemma recipLoad_pos_of_window (D : R2ConcreteData T b) (hb : 0 < b)
    (hlb : 3 / (2 * (b : ℝ)) ≤ recipLoad D.E) :
    0 < recipLoad D.E := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hgap : 0 < 3 / (2 * (b : ℝ)) := by positivity
  exact lt_of_lt_of_le hgap hlb

lemma uniformTheta_lower_of_window (D : R2ConcreteData T b) (hb : 0 < b)
    (hlb : 3 / (2 * (b : ℝ)) ≤ recipLoad D.E)
    (hub : recipLoad D.E < 3 / (b : ℝ)) :
    1 / 3 ≤ (1 / (b : ℝ)) / recipLoad D.E := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hSpos : 0 < recipLoad D.E := recipLoad_pos_of_window D hb hlb
  have hc :
      (1 / (b : ℝ)) / recipLoad D.E =
        1 / ((b : ℝ) * recipLoad D.E) := by
    field_simp [hbR.ne', hSpos.ne']
  rw [hc]
  have hle : (b : ℝ) * recipLoad D.E ≤ 3 := by
    have hmul := mul_lt_mul_of_pos_left hub hbR
    field_simp [hbR.ne'] at hmul
    exact le_of_lt hmul
  exact one_div_le_one_div_of_le (mul_pos hbR hSpos) hle

lemma uniformTheta_upper_of_window (D : R2ConcreteData T b) (hb : 0 < b)
    (hlb : 3 / (2 * (b : ℝ)) ≤ recipLoad D.E) :
    (1 / (b : ℝ)) / recipLoad D.E ≤ 2 / 3 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hSpos : 0 < recipLoad D.E := recipLoad_pos_of_window D hb hlb
  have hc :
      (1 / (b : ℝ)) / recipLoad D.E =
        1 / ((b : ℝ) * recipLoad D.E) := by
    field_simp [hbR.ne', hSpos.ne']
  rw [hc]
  have hge : 3 ≤ 2 * ((b : ℝ) * recipLoad D.E) := by
    have hmul := mul_le_mul_of_nonneg_left hlb
      (by positivity : (0 : ℝ) ≤ 2 * (b : ℝ))
    field_simp [hbR.ne'] at hmul
    nlinarith
  rw [div_le_div_iff₀ (mul_pos hbR hSpos) (by norm_num : (0 : ℝ) < 3)]
  nlinarith

lemma uniformTheta_mass (D : R2ConcreteData T b) (hb : 0 < b)
    (hlb : 3 / (2 * (b : ℝ)) ≤ recipLoad D.E) :
    (∑ e ∈ D.E, uniformTheta D e / (e : ℝ)) = 1 / (b : ℝ) := by
  have hSpos : 0 < recipLoad D.E := recipLoad_pos_of_window D hb hlb
  have hSpos' : 0 < ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) := by
    simpa [recipLoad] using hSpos
  unfold uniformTheta recipLoad
  calc
    (∑ e ∈ D.E,
        ((1 / (b : ℝ)) / ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ)) / (e : ℝ))
        = ∑ e ∈ D.E,
            ((1 / (b : ℝ)) / ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ)) *
              ((1 : ℝ) / (e : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          ring
    _ = ((1 / (b : ℝ)) / ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ)) *
          ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) := by
          rw [Finset.mul_sum]
    _ = 1 / (b : ℝ) := by
          rw [div_mul_cancel₀ _ hSpos'.ne']

/-- Build the final weight package from the concrete reciprocal-load window. -/
def weights_of_recipLoad_window (D : R2ConcreteData T b) (hb : 0 < b)
    (hlb : 3 / (2 * (b : ℝ)) ≤ recipLoad D.E)
    (hub : recipLoad D.E < 3 / (b : ℝ)) :
    Weights D where
  theta := uniformTheta D
  hlb := by
    intro e he
    exact uniformTheta_lower_of_window D hb hlb hub
  hub := by
    intro e he
    exact uniformTheta_upper_of_window D hb hlb
  hmass := uniformTheta_mass D hb hlb

end R2ConcreteData

end CircleMethod

end
