module

public import PeriodThree.ExactPeriods
public import PeriodThree.Reflection

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by the orientation arithmetic proof)

/-!
# Exact periods under either Li-Yorke orbit order

This file combines the verified increasing-order construction with reflection
to prove part T1 of [LY75, Theorem I and its proof, pp. 987-988] in both orientations.
-/

@[expose] public section

open Set

namespace PeriodThree

/-- Under either Li-Yorke orbit-order alternative, every positive integer is
the exact least period of a point in the interval. This is part T1 of [LY75,
Theorem I, p. 987]. -/
theorem existsPointOfLeastPeriodOfOrbitOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J) (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : OrbitOrder F a) :
    ∀ k : ℕ, 0 < k → ∃ x ∈ J, Function.minimalPeriod F x = k := by
  rcases horder with hincreasing | hdecreasing
  · exact existsPointOfLeastPeriodOfIncreasingOrder hJ hF hFJ haJ hincreasing
  · have hreflectedOrder :
        ((reverseMap F)^[3]) (-a) ≤ -a ∧
          -a < reverseMap F (-a) ∧
            reverseMap F (-a) < ((reverseMap F)^[2]) (-a) := by
      simp only [reverseMapIterate, reverseMap, neg_neg]
      constructor
      · linarith [hdecreasing.1]
      constructor <;> linarith [hdecreasing.2.1, hdecreasing.2.2]
    intro k hk
    obtain ⟨x, hxJ, hxperiod⟩ :=
      existsPointOfLeastPeriodOfIncreasingOrder
        (PeriodThree.OrdConnected.negSet hJ)
        (PeriodThree.ContinuousOn.reflected hF)
        (PeriodThree.MapsTo.reflected hFJ) (by simpa [negSet] using haJ)
        hreflectedOrder k hk
    refine ⟨-x, hxJ, ?_⟩
    simpa using hxperiod

end PeriodThree
