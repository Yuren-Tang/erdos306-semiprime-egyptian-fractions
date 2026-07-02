import RequestProject.GlobalControl.Encoding.DominantLabels

/-!
# Cold-block structure

Exceptional primes and conforming dominant-label classes in a cold block.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- Primes of block `k` where the assignment differs from its canonical
dominant label. -/
def excSet (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : Finset ℕ :=
  (BS.P k).filter (fun p => toPlain BS a p ≠ ((coldLabel BS a k : ℤ) : ZMod p))

lemma excSet_subset (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    excSet BS a k ⊆ BS.P k := Finset.filter_subset _ _

/-- On a block in the block-system range, restriction agrees with extension
to a plain assignment. -/
lemma restrict_eq_toPlain (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (_hk : k ∈ Finset.Icc BS.k0 BS.K) (p : {p : ℕ // p ∈ BS.P k}) :
    restrict BS a k p = toPlain BS a (p : ℕ) := by
  unfold restrict toPlain
  simp +decide [*]

/-- The global exception count agrees with the attached block-assignment
exception count. -/
lemma excSet_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (excSet BS a k).card =
      ((BS.P k).attach.filter
        (fun q => restrict BS a k q ≠ ((coldLabel BS a k : ℤ) : ZMod (q : ℕ)))).card := by
  convert Finset.card_image_iff.mpr _ using 1
  rotate_left
  exact ℕ
  exact fun q => q.val
  infer_instance
  · exact fun x _ y _ hxy => Subtype.ext hxy
  · congr! 1
    ext
    simp [excSet]
    exact ⟨fun h => ⟨h.1, by simpa [restrict_eq_toPlain BS a k hk] using h.2⟩,
      fun h => ⟨h.1, by simpa [restrict_eq_toPlain BS a k hk] using h.2⟩⟩

/-- The conforming primes are exactly the dominant-label class. -/
lemma conform_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (BS.P k \ excSet BS a k).card = classCount BS a k (coldLabel BS a k) := by
  refine' Finset.card_bij _ _ _ _
  use fun x hx => ⟨x, (Finset.mem_sdiff.mp hx).1⟩
  · simp +contextual [restrict_eq_toPlain BS a k hk, excSet]
  · aesop
  · simp +decide [excSet, restrict_eq_toPlain BS a k hk]
    tauto

end GlobalControl

end
