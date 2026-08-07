import BoundedGaps.Maynard.ConcreteFractionalRectangle

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set

theorem eventually_engelsmaFractionalTupleShell_subset_preSievedSimplexTupleSupport
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta gamma : H → ℝ)
    (hgamma : ∀ h, 0 ≤ gamma h)
    (hsum : ∑ h : H, gamma h < 1) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaFractionalTupleShell H alpha beta gamma N ⊆
        preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) := by
  have hbox := eventually_engelsmaFractionalTupleBox_subset_preSievedSimplexTupleSupport
    halpha gamma hgamma hsum
  filter_upwards [hbox] with N hboxN
  intro u hu
  apply hboxN
  rw [engelsmaFractionalTupleBox, squarefreeCoprimeTupleBox,
    Fintype.mem_piFinset]
  intro h
  have huShell : u ∈ squarefreeCoprimeTupleShell H
      (engelsmaMaynardModulus N)
      (fun h => engelsmaMaynardRadius (alpha * beta h) N)
      (fun h => engelsmaMaynardRadius (alpha * gamma h) N) := by
    simpa [engelsmaFractionalTupleShell] using hu
  have huh := Fintype.mem_piFinset.mp huShell h
  exact Finset.mem_sdiff.mp huh |>.1

end BoundedGaps.Maynard
