import BoundedGaps.Maynard.MaynardS2RestrictedCrossStarredSupport

noncomputable section

/-!
# Exact starred rough reindex of the restricted S2 cross correction

The factored nontrivial cross sum is restricted first to tuples with supported
coordinate-one lower faces and starred coprimality, then to the rough
primorial cross support. Both restrictions are exact finite identities.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance restrictedS2StarredRoughSumDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def nontrivialRestrictedS2CoefficientFactoredSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (maynardS2G (u h) : ℝ)) *
            restrictedS2LeftCoefficientFactor H R W y m u s *
            restrictedS2RightCoefficientFactor H R W y m u s
    else 0

def nontrivialRestrictedS2StarredFactoredSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsRestrictedS2StarredCrossTuple H R W m u s then
            (∏ h : H, (maynardS2G (u h) : ℝ)) *
              restrictedS2LeftCoefficientFactor H R W y m u s *
              restrictedS2RightCoefficientFactor H R W y m u s
          else 0
    else 0

def nontrivialRestrictedS2StarredRoughFactoredSum
    (H : Finset ℕ) (R D : ℕ) (y : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ s ∈ roughCrossTupleSupport H D R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            (∏ h : H, (maynardS2G (u h) : ℝ)) *
              restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
              restrictedS2RightCoefficientFactor H R (primorial D) y m u s
          else 0
    else 0

theorem nontrivialRestrictedS2AuxiliaryFactoredSum_eq_coefficientFactoredSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) (m : H) :
    nontrivialRestrictedS2AuxiliaryFactoredSum H R
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m =
      nontrivialRestrictedS2CoefficientFactoredSum H R W y m := by
  rfl

theorem nontrivialRestrictedS2CoefficientFactoredSum_eq_starred
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H) :
    nontrivialRestrictedS2CoefficientFactoredSum H R W y m =
      nontrivialRestrictedS2StarredFactoredSum H R W y m := by
  classical
  unfold nontrivialRestrictedS2CoefficientFactoredSum
    nontrivialRestrictedS2StarredFactoredSum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe, if_pos hsNe]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hstar : IsRestrictedS2StarredCrossTuple H R W m u s
    · rw [if_pos hstar]
    · rw [if_neg hstar]
      by_cases hl :
          restrictedS2LeftCoefficientFactor H R W y m u s = 0
      · simp [hl]
      · have hr :
            restrictedS2RightCoefficientFactor H R W y m u s = 0 := by
          by_contra hr
          exact hstar
            (isRestrictedS2StarredCrossTuple_of_factors_ne_zero
              m hu hs hl hr)
        simp [hr]
  · rw [if_neg hsNe, if_neg hsNe]

theorem nontrivialRestrictedS2StarredFactoredSum_eq_rough
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    (hR : 0 < R) :
    nontrivialRestrictedS2StarredFactoredSum H R (primorial D) y m =
      nontrivialRestrictedS2StarredRoughFactoredSum H R D y m := by
  classical
  unfold nontrivialRestrictedS2StarredFactoredSum
    nontrivialRestrictedS2StarredRoughFactoredSum
  apply (Finset.sum_subset
    (roughCrossTupleSupport_subset_crossMoebiusTupleBox hR) ?_).symm
  intro s hsBox hsNotRough
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hstar :
        IsRestrictedS2StarredCrossTuple H R (primorial D) m u s
    · rw [if_pos hstar]
      have hl : restrictedS2LeftCoefficientFactor H R (primorial D) y m u s =
          0 := by
        by_contra hl
        exact hsNotRough
          (roughCrossTupleSupport_of_restrictedS2LeftFactor_ne_zero
            m hu hsBox hl)
      simp [hl]
    · rw [if_neg hstar]
  · rw [if_neg hsNe]

theorem incompatibleRestrictedS2_eq_neg_starredRoughFactoredSum
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    (hR : 0 < R) :
    incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) m =
      -nontrivialRestrictedS2StarredRoughFactoredSum H R D y m := by
  have hSupport : ∀ d ∈ maynardDivisorTupleSupport H R (primorial D),
      IsMaynardDivisorTuple H R (primorial D) d := by
    intro d hd
    exact isMaynardDivisorTuple_of_mem_support hd
  calc
    incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) m =
        -nontrivialRestrictedS2AuxiliaryMobiusSum H R
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m :=
      incompatibleRestrictedS2_eq_neg_nontrivial m hSupport
    _ = -nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum H R
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m := by
      rw [nontrivialRestrictedS2AuxiliaryMobiusSum_eq_globalQuadrupleSum
        m hSupport]
    _ = -nontrivialRestrictedS2AuxiliaryFactoredSum H R
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m := by
      rw [restrictedS2GlobalQuadrupleSum_eq_factoredSum]
    _ = -nontrivialRestrictedS2CoefficientFactoredSum H R (primorial D) y m := by
      rw [nontrivialRestrictedS2AuxiliaryFactoredSum_eq_coefficientFactoredSum]
    _ = -nontrivialRestrictedS2StarredFactoredSum H R (primorial D) y m := by
      rw [nontrivialRestrictedS2CoefficientFactoredSum_eq_starred]
    _ = -nontrivialRestrictedS2StarredRoughFactoredSum H R D y m := by
      rw [nontrivialRestrictedS2StarredFactoredSum_eq_rough m hR]

end BoundedGaps.Maynard
