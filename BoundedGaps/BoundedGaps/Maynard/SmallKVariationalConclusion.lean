import BoundedGaps.Maynard.SmallKFaceMoments
import BoundedGaps.Maynard.VariationalBoundedness

/-! # The checked `M_105 > 4` conclusion -/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem maynardNumerator_eq_smallKNumerator :
    (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      (smallKNumerator : ℝ) :=
  maynardNumerator_eq_smallKNumerator_of_face_moments
    (fun i j => smallKRealFacePairTerm_moment_sum i j)

theorem smallKCandidate_ratio_gt_four :
    (4 : ℝ) < maynardRatio 105 smallKCandidate :=
  smallK_candidate_ratio_gt_four_of_functionals
    maynardI_eq_smallKDenominator maynardNumerator_eq_smallKNumerator

theorem maynardM_105_gt_four : (4 : ℝ) < maynardM 105 :=
  maynardM_gt_four_of_bddAbove maynardRatioSet_105_bddAbove

end BoundedGaps.Maynard
