import RequestProject.Core.IntervalSegmentation
import RequestProject.GlobalControl.Encoding.DominantLabels

/-!
# Fibers of the global block encoding

Assignment fibers determined by energy shells and segment labels, together with
their product bound from block restriction.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- The data-fiber of `(H,B,v,ℓ)`: assignments whose every
    block energy sits in the shell `v k` and whose cold blocks carry the
    segment-start label `ℓ (RequestProject.segmentStart …)` on a `(1-ρ)` fraction of primes. -/
def fiber (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    Finset (GlobalAssignment BS) :=
  Finset.univ.filter (fun a => ∀ k ∈ Finset.Icc BS.k0 BS.K,
    blockEnergy BS a k ≤ (v k : ℝ) + 1 ∧
    (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (classCount BS a k (ℓ (RequestProject.segmentStart BS.k0 H B k)) : ℝ)))

/-
The fiber injects into the product of the
    per-block counts (Lemma D4, `restrict_filter_card_le`).
-/
lemma fiber_card_le (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    (fiber BS H B v ℓ).card ≤
      ∏ k ∈ Finset.Icc BS.k0 BS.K,
        (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
          QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
          (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
            (((BS.P k).attach.filter
              (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card := by
  unfold fiber; norm_num;
  convert restrict_filter_card_le BS ( fun k b => QP ( BS.P k ) b ≤ v k + 1 ∧ ( k ∉ H → ( 3 / 4 : ℝ ) * ( BS.P k |> Finset.card ) ≤ ( Finset.card ( Finset.filter ( fun p : { x // x ∈ BS.P k } => b p = ℓ ( RequestProject.segmentStart BS.k0 H B k ) ) ( Finset.attach ( BS.P k ) ) ) : ℝ ) ) ) using 2;
  · simp +decide [ blockEnergy, classCount ];
  · convert rfl

end GlobalControl

end
