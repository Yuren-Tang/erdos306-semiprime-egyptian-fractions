import RequestProject.GlobalControl.Encoding.BlockData
import RequestProject.LocalEnergy.DominantLabel

/-! Fixed-label entropy bounds for cold blocks. -/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
Per-cold-block fixed-label count: for a label
    of size `|m| ≤ N·X/16` the number of block assignments of energy `≤ n+1`
    whose `m`-class covers a `(1-ρ)` fraction is `≤ exp(ε(n+1))`.  Direct wrapper
    of `LocalEnergy.fixed_label_level_set_bound` at `ρ = 1/4`.
-/
lemma fixed_label_block_count (eps : ℝ) (heps : 0 < eps) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ), |(m : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 →
        ∀ (n : ℕ),
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (eps * ((n : ℝ) + 1)) := by
  obtain ⟨ X0, hX0, hF ⟩ := LocalEnergy.fixed_label_level_set_bound eps ( 1 / 4 ) heps ( by norm_num ) ( by norm_num );
  refine' ⟨ ⌈X0⌉₊ + 1, by positivity, fun BS k hk1 hk2 hk3 m hm n ↦ _ ⟩;
  convert hF ( 2 ^ k ) _ ( BS.P k ) _ _ m _ ( n + 1 ) _ using 1 <;> norm_num;
  · linarith [ Nat.le_ceil X0 ];
  · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
  · convert BS.hdensity k hk1 hk2 |> le_trans _ using 1 ; ring_nf;
    norm_num [ Real.log_pow ] ; ring_nf ; norm_num;
  · convert hm using 1

end GlobalControl

end
