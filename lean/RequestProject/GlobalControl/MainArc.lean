import RequestProject.GlobalControl.Basic

noncomputable section

namespace GlobalControl

/-- The main arc consists of globally diagonal assignments whose common label
has size at most `C / sigmaCtrl BS`. -/
def mainArc (BS : BlockSystem) (C : ℝ) : Set (GlobalAssignment BS) :=
  {a | ∃ m : ℤ, |(m : ℝ)| ≤ C / sigmaCtrl BS ∧
        ∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1)}

end GlobalControl

end
