import RequestProject.BlockMassPool
import RequestProject.ExtraEnergyMinorArc
import RequestProject.ExtraMinorDamping
import RequestProject.ArcConstructionSigma

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 assembly skeleton

This leaf collects the finite edge-set bookkeeping needed before the final
`exists_arcConstruction` assembly: gadget edges, their period divisibility, and
the semiprime/avoidance bookkeeping for `ctrlEdges ∪ Q ∪ gadgetEdges`.
-/

/-- Gadget edges `r*s`, where `r` is a denominator prime and `s` is a chosen block
support prime. -/
def gadgetEdges (R S : Finset ℕ) : Finset ℕ :=
  (R ×ˢ S).image (fun rs : ℕ × ℕ => rs.1 * rs.2)

lemma mem_gadgetEdges {R S : Finset ℕ} {e : ℕ} :
    e ∈ gadgetEdges R S ↔ ∃ r ∈ R, ∃ s ∈ S, e = r * s := by
  constructor
  · intro he
    rw [gadgetEdges, Finset.mem_image] at he
    obtain ⟨rs, hrs, rfl⟩ := he
    rw [Finset.mem_product] at hrs
    exact ⟨rs.1, hrs.1, rs.2, hrs.2, rfl⟩
  · intro he
    obtain ⟨r, hr, s, hs, rfl⟩ := he
    rw [gadgetEdges, Finset.mem_image]
    exact ⟨(r, s), by simpa [Finset.mem_product] using And.intro hr hs, rfl⟩

lemma gadgetEdges_semiprime {R S : Finset ℕ}
    (hRprime : ∀ r ∈ R, Nat.Prime r)
    (hSprime : ∀ s ∈ S, Nat.Prime s)
    (hlt : ∀ r ∈ R, ∀ s ∈ S, r < s) :
    ∀ e ∈ gadgetEdges R S, IsSemiprime e := by
  intro e he
  rw [mem_gadgetEdges] at he
  obtain ⟨r, hr, s, hs, rfl⟩ := he
  exact ⟨r, s, hRprime r hr, hSprime s hs, hlt r hr s hs, rfl⟩

lemma gadgetEdges_dvd_period {BS : BlockSystem} {R S : Finset ℕ} {b e : ℕ}
    (he : e ∈ gadgetEdges R S)
    (hRdvd : ∀ r ∈ R, r ∣ b)
    (hSblock : S ⊆ blockSupport BS) :
    e ∣ primeSupportPeriod b (blockSupport BS) := by
  rw [mem_gadgetEdges] at he
  obtain ⟨r, hr, s, hs, rfl⟩ := he
  obtain ⟨ar, har⟩ := hRdvd r hr
  have hsblock : s ∈ blockSupport BS := hSblock hs
  have hsdvd : s ∣ ∏ p ∈ blockSupport BS, p := Finset.dvd_prod_of_mem id hsblock
  obtain ⟨as, has⟩ := hsdvd
  refine ⟨ar * as, ?_⟩
  rw [primeSupportPeriod, har, has]
  ring

lemma gadgetEdges_avoid_of_pair_avoid {R S T : Finset ℕ}
    (havoid : ∀ r ∈ R, ∀ s ∈ S, r * s ∉ T) :
    ∀ e ∈ gadgetEdges R S, e ∉ T := by
  intro e he
  rw [mem_gadgetEdges] at he
  obtain ⟨r, hr, s, hs, rfl⟩ := he
  exact havoid r hr s hs

/-- The provisional R2 edge set before final parameter choices. -/
def r2Edges (BS : BlockSystem) (Q R S : Finset ℕ) : Finset ℕ :=
  ctrlEdges BS ∪ Q ∪ gadgetEdges R S

lemma ctrlEdges_subset_r2Edges (BS : BlockSystem) (Q R S : Finset ℕ) :
    ctrlEdges BS ⊆ r2Edges BS Q R S := by
  intro e he
  simp [r2Edges, he]

lemma massBatch_subset_r2Edges (BS : BlockSystem) (Q R S : Finset ℕ) :
    Q ⊆ r2Edges BS Q R S := by
  intro e he
  simp [r2Edges, he]

lemma gadgetEdges_subset_r2Edges (BS : BlockSystem) (Q R S : Finset ℕ) :
    gadgetEdges R S ⊆ r2Edges BS Q R S := by
  intro e he
  simp [r2Edges, he]

lemma r2_edges_semiprime {BS : BlockSystem} {Q R S : Finset ℕ}
    (hQsemi : ∀ e ∈ Q, IsSemiprime e)
    (hRprime : ∀ r ∈ R, Nat.Prime r)
    (hSprime : ∀ s ∈ S, Nat.Prime s)
    (hlt : ∀ r ∈ R, ∀ s ∈ S, r < s) :
    ∀ e ∈ r2Edges BS Q R S, IsSemiprime e := by
  intro e he
  rw [r2Edges, Finset.mem_union] at he
  rcases he with hctrlQ | hgadget
  · rw [Finset.mem_union] at hctrlQ
    rcases hctrlQ with hctrl | hQ
    · exact ctrlEdges_semiprime BS hctrl
    · exact hQsemi e hQ
  · exact gadgetEdges_semiprime hRprime hSprime hlt e hgadget

lemma r2_edges_avoid {BS : BlockSystem} {Q R S T : Finset ℕ}
    (hctrl : ∀ e ∈ ctrlEdges BS, e ∉ T)
    (hQ : ∀ e ∈ Q, e ∉ T)
    (hgadget : ∀ e ∈ gadgetEdges R S, e ∉ T) :
    ∀ e ∈ r2Edges BS Q R S, e ∉ T := by
  intro e he
  rw [r2Edges, Finset.mem_union] at he
  rcases he with hctrlQ | hg
  · rw [Finset.mem_union] at hctrlQ
    rcases hctrlQ with hc | hq
    · exact hctrl e hc
    · exact hQ e hq
  · exact hgadget e hg

lemma r2_edges_dvd_period {BS : BlockSystem} {Q R S : Finset ℕ} {b e : ℕ}
    (he : e ∈ r2Edges BS Q R S)
    (hQdvd : ∀ e ∈ Q, e ∣ primeSupportPeriod b (blockSupport BS))
    (hRdvd : ∀ r ∈ R, r ∣ b)
    (hSblock : S ⊆ blockSupport BS) :
    e ∣ primeSupportPeriod b (blockSupport BS) := by
  rw [r2Edges, Finset.mem_union] at he
  rcases he with hctrlQ | hgadget
  · rw [Finset.mem_union] at hctrlQ
    rcases hctrlQ with hctrl | hQ
    · have hctrlSupport :
          e ∣ ∏ p ∈ blockSupport BS, p := by
        exact semiprime_dvd_edgePrimeSupport_prod hctrl (ctrlEdges_semiprime BS hctrl) |>.trans
          (Finset.prod_dvd_prod_of_subset (edgePrimeSupport (ctrlEdges BS)) (blockSupport BS) id
            (edgePrimeSupport_ctrlEdges_subset_blockSupport BS))
      exact edge_dvd_primeSupportPeriod_of_mem_support hctrlSupport
    · exact hQdvd e hQ
  · exact gadgetEdges_dvd_period hgadget hRdvd hSblock

end CircleMethod

end
