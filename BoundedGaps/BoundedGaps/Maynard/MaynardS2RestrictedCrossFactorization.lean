import BoundedGaps.Maynard.MaynardS2RestrictedCrossMobius
import BoundedGaps.Maynard.MaynardS1GlobalCrossReindex

noncomputable section

/-!
# Fixed-box factorization of the restricted S2 cross correction

The exact nontrivial cross sum is reindexed to independent cross and common
divisor boxes. The distinguished coordinate-one condition remains in both
coefficient factors.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2RestrictedCrossFactorDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def restrictedS2LeftCrossDivides
    (H : Finset ℕ) (m : H) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (d : H → ℕ) : Prop :=
  LeftCrossDivides H u s d ∧ d m = 1

def restrictedS2RightCrossDivides
    (H : Finset ℕ) (m : H) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (e : H → ℕ) : Prop :=
  RightCrossDivides H u s e ∧ e m = 1

def nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ crossMoebiusTupleBox H R,
    ∑ u ∈ maynardDivisorTupleBox H R,
      if s ≠ oneCrossMoebiusTuple H ∧
          restrictedS2LeftCrossDivides H m u s d ∧
          restrictedS2RightCrossDivides H m u s e then
        crossMoebiusTupleTerm H s *
          ((∏ h : H, (maynardS2G (u h) : ℝ)) *
            ((lambda d / divisorTupleTotientProduct H d) *
              (lambda e / divisorTupleTotientProduct H e)))
      else 0

def nontrivialRestrictedS2AuxiliaryFactoredSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (maynardS2G (u h) : ℝ)) *
            (∑ d ∈ D, if restrictedS2LeftCrossDivides H m u s d then
              lambda d / divisorTupleTotientProduct H d else 0) *
            (∑ e ∈ D, if restrictedS2RightCrossDivides H m u s e then
              lambda e / divisorTupleTotientProduct H e else 0)
    else 0

theorem nontrivialRestrictedS2AuxiliaryMobiusSum_eq_globalQuadrupleSum
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    nontrivialRestrictedS2AuxiliaryMobiusSum H R D lambda m =
      nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum H R D lambda m := by
  classical
  unfold nontrivialRestrictedS2AuxiliaryMobiusSum
    nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hsFilter := filter_crossMoebiusTupleBox_ne_one_eq_erase_support
    (hD d hd) (e := e)
  rw [← hsFilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsCond : s ≠ oneCrossMoebiusTuple H ∧ CrossTupleDivides H s d e
  · rw [if_pos hsCond]
    rw [sum_commonDivisorTuple_eq_box_indicator (hD d hd)]
    by_cases hm : d m = 1 ∧ e m = 1
    · rw [if_pos hm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases huCond : ∀ h : H, u h ∣ d h ∧ u h ∣ e h
      · rw [if_pos huCond]
        have hlr := cross_and_common_iff_left_right.mp
          ⟨hsCond.2, huCond⟩
        rw [if_pos ⟨hsCond.1, ⟨hlr.1, hm.1⟩,
              ⟨hlr.2, hm.2⟩⟩]
        rw [commonDivisorS2TupleTerm_eq_product_div]
        simp only [div_eq_mul_inv]
        ring
      · rw [if_neg huCond]
        have hnot : ¬(s ≠ oneCrossMoebiusTuple H ∧
            restrictedS2LeftCrossDivides H m u s d ∧
            restrictedS2RightCrossDivides H m u s e) := by
          rintro ⟨hsNe, hl, hr⟩
          exact huCond (cross_and_common_iff_left_right.mpr
            ⟨hl.1, hr.1⟩).2
        rw [if_neg hnot]
        simp
    · rw [if_neg hm]
      symm
      rw [mul_zero]
      apply Finset.sum_eq_zero
      intro u hu
      rw [if_neg]
      intro h
      exact hm ⟨h.2.1.2, h.2.2.2⟩
  · rw [if_neg hsCond]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [if_neg]
    intro h
    have hcross : CrossTupleDivides H s d e :=
      (cross_and_common_iff_left_right.mpr
        ⟨h.2.1.1, h.2.2.1⟩).1
    exact hsCond ⟨h.1, hcross⟩

theorem restrictedS2GlobalQuadrupleSum_eq_factoredSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) :
    nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum H R D lambda m =
      nontrivialRestrictedS2AuxiliaryFactoredSum H R D lambda m := by
  classical
  unfold nontrivialRestrictedS2AuxiliaryGlobalQuadrupleSum
    nontrivialRestrictedS2AuxiliaryFactoredSum
  let S := crossMoebiusTupleBox H R
  let U := maynardDivisorTupleBox H R
  let F := fun
      (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
      (u d e : H → ℕ) =>
    if s ≠ oneCrossMoebiusTuple H ∧
        restrictedS2LeftCrossDivides H m u s d ∧
        restrictedS2RightCrossDivides H m u s e then
      crossMoebiusTupleTerm H s *
        ((∏ h : H, (maynardS2G (u h) : ℝ)) *
          ((lambda d / divisorTupleTotientProduct H d) *
            (lambda e / divisorTupleTotientProduct H e)))
    else 0
  change (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) = _
  calc
    (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) =
        ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ e ∈ D, F s u d e := by
      calc
        (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) =
            ∑ d ∈ D, ∑ s ∈ S, ∑ e ∈ D, ∑ u ∈ U, F s u d e := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ U, F s u d e := by
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ d ∈ D, ∑ u ∈ U, ∑ e ∈ D, F s u d e := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ e ∈ D, F s u d e := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_comm]
    _ = ∑ s ∈ S,
        if s ≠ oneCrossMoebiusTuple H then
          crossMoebiusTupleTerm H s *
            ∑ u ∈ U,
              (∏ h : H, (maynardS2G (u h) : ℝ)) *
                (∑ d ∈ D, if restrictedS2LeftCrossDivides H m u s d then
                  lambda d / divisorTupleTotientProduct H d else 0) *
                (∑ e ∈ D, if restrictedS2RightCrossDivides H m u s e then
                  lambda e / divisorTupleTotientProduct H e else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsNe : s ≠ oneCrossMoebiusTuple H
      · rw [if_pos hsNe, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [show
          crossMoebiusTupleTerm H s *
              (((∏ h : H, (maynardS2G (u h) : ℝ)) *
                (∑ d ∈ D, if restrictedS2LeftCrossDivides H m u s d then
                  lambda d / divisorTupleTotientProduct H d else 0)) *
                (∑ e ∈ D, if restrictedS2RightCrossDivides H m u s e then
                  lambda e / divisorTupleTotientProduct H e else 0)) =
            (crossMoebiusTupleTerm H s *
              (∏ h : H, (maynardS2G (u h) : ℝ))) *
              ((∑ d ∈ D, if restrictedS2LeftCrossDivides H m u s d then
                lambda d / divisorTupleTotientProduct H d else 0) *
              (∑ e ∈ D, if restrictedS2RightCrossDivides H m u s e then
                lambda e / divisorTupleTotientProduct H e else 0)) by ring]
        rw [mul_filtered_sums_eq_pair_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        dsimp [F]
        by_cases hl : restrictedS2LeftCrossDivides H m u s d
        · by_cases hr : restrictedS2RightCrossDivides H m u s e
          · rw [if_pos ⟨hsNe, hl, hr⟩, if_pos ⟨hl, hr⟩]
            ring
          · simp [hr]
        · simp [hl]
      · rw [if_neg hsNe]
        apply Finset.sum_eq_zero
        intro u hu
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro e he
        dsimp [F]
        rw [if_neg (fun h => hsNe h.1)]

end BoundedGaps.Maynard
