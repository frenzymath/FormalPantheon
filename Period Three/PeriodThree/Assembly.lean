module

public import PeriodThree.Statement

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by the assembly arithmetic proof)
import PeriodThree.AllPeriods -- shake: keep (decreasing-branch transport)
import PeriodThree.Scrambled.Separation

/-!
# Assembly of the two orbit-order branches

This file combines the exact-period and scrambled-set constructions for the
increasing branch, then transports the decreasing branch by reflection. It is
the final proof-support layer for [LY75, Theorem I, p. 987].
-/

public section

open Set

namespace PeriodThree

/-- The increasing orbit-order branch has every clause of Theorem I
[LY75, Theorem I, p. 987]. -/
theorem theoremIConclusionOfIncreasingOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J)
    (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) :
    TheoremIConclusion F J := by
  refine ⟨existsPointOfLeastPeriodOfIncreasingOrder hJ hF hFJ haJ horder, ?_⟩
  exact existsLiYorkeScrambledSetOfIncreasingOrder hJ hF hFJ haJ horder

/-- Either orbit-order alternative has the full conclusion of Li and Yorke's
Theorem I [LY75, Theorem I, p. 987]. -/
theorem theoremIConclusionOfOrbitOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J)
    (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : OrbitOrder F a) :
    TheoremIConclusion F J := by
  rcases horder with hincreasing | hdecreasing
  · exact theoremIConclusionOfIncreasingOrder hJ hF hFJ haJ hincreasing
  · have hreflectedOrder :
        ((reverseMap F)^[3]) (-a) ≤ -a ∧
          -a < reverseMap F (-a) ∧
            reverseMap F (-a) < ((reverseMap F)^[2]) (-a) := by
      simp only [reverseMapIterate, reverseMap, neg_neg]
      constructor
      · linarith [hdecreasing.1]
      constructor <;> linarith [hdecreasing.2.1, hdecreasing.2.2]
    have hreflectedConclusion :
        TheoremIConclusion (reverseMap F) (negSet J) :=
      theoremIConclusionOfIncreasingOrder
        (PeriodThree.OrdConnected.negSet hJ)
        (PeriodThree.ContinuousOn.reflected hF)
        (PeriodThree.MapsTo.reflected hFJ)
        (by simpa [negSet] using haJ) hreflectedOrder
    exact (theoremIConclusionReverseMapIff F J).mp hreflectedConclusion

end PeriodThree
