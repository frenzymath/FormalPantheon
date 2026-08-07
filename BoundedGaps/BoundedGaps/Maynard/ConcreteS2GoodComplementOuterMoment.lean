import BoundedGaps.Maynard.ConcreteS2EndpointIntegralSquare
import BoundedGaps.Maynard.MaynardS2OuterFaceBox

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory
open scoped BigOperators

noncomputable def engelsmaS2CoordinateFiberGoodComplementOuterMoment
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
    maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) *
      ((Real.log R) *
        (∫ x in (0 : ℝ)..(
          1 - Real.log (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r) / Real.log R),
          engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2

set_option maxRecDepth 5000 in
theorem engelsmaS2CoordinateFiberGoodOuterMass_le_faceBox
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    (∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
      maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) ≤
      ∏ _ ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
  let G := engelsmaS2CoordinateFiberGoodSupport R D m
  let F := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ∏ h : BoundedGaps.engelsmaTuple,
      maynardS2OuterSquarefreeAF (primorial D) (r h)
  have hrewrite : ∀ r ∈ G,
      maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) =
        F r := by
    intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hfac := maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod m r
      (isMaynardDivisorTuple_of_mem_support hrData.1)
    have hrm : r m = 1 := hrData.2.1
    unfold F
    calc
      maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) =
          ∏ h ∈ Finset.univ.erase m,
            maynardS2OuterSquarefreeAF (primorial D) (r h) := hfac
      _ = maynardS2OuterSquarefreeAF (primorial D) (r m) *
          ∏ h ∈ Finset.univ.erase m,
            maynardS2OuterSquarefreeAF (primorial D) (r h) := by
        rw [hrm]
        simp only [(maynardS2OuterSquarefreeAF_isMultiplicative
          (primorial D)).map_one, one_mul]
      _ = ∏ h : BoundedGaps.engelsmaTuple,
          maynardS2OuterSquarefreeAF (primorial D) (r h) :=
        Finset.mul_prod_erase Finset.univ
          (fun h : BoundedGaps.engelsmaTuple =>
            maynardS2OuterSquarefreeAF (primorial D) (r h))
          (Finset.mem_univ m)
  have hsum : (∑ r ∈ G, F r) ≤
      ∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m, F r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact engelsmaS2CoordinateFiberGoodSupport_subset_outerFaceBox R D m
    · intro r hrBox hrNot
      unfold F
      apply Finset.prod_nonneg
      intro h hh
      exact maynardS2OuterSquarefreeAF_nonneg _ _
  calc
    (∑ r ∈ G,
      maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) =
        ∑ r ∈ G, F r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hrewrite r hr
    _ ≤ ∑ r ∈ maynardS2OuterCoordinateOneFaceBox R D m, F r := hsum
    _ = ∏ h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
      exact maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean m

set_option maxRecDepth 6000 in
theorem abs_engelsmaS2CoordinateFiberGoodOuterMoment_sub_complement_le_faceBox
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hR : 1 < R) :
    |engelsmaS2CoordinateFiberGoodOuterMoment R D m -
        engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
      ((smallKCandidateBound * Real.log 3) *
        (2 * (Real.log R * smallKCandidateBound) +
          smallKCandidateBound * Real.log 3)) *
        ∏ _ ∈ Finset.univ.erase m,
          maynardS2OuterSquarefreeMean (primorial D) R := by
  let G := engelsmaS2CoordinateFiberGoodSupport R D m
  let A := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    maynardS2OuterSquarefreeAF (primorial D)
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let I := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ((Real.log R) *
      (∫ x in (0 : ℝ)..(
        Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2
  let J := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ((Real.log R) *
      (∫ x in (0 : ℝ)..(
        1 - Real.log (maynardS2OffCoordinateProduct
          BoundedGaps.engelsmaTuple m r) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2
  let B := (smallKCandidateBound * Real.log 3) *
    (2 * (Real.log R * smallKCandidateBound) +
      smallKCandidateBound * Real.log 3)
  have hE : 0 ≤ smallKCandidateBound * Real.log 3 :=
    mul_nonneg smallKCandidateBound_nonneg
      (Real.log_nonneg (by norm_num))
  have hRlog : 0 ≤ Real.log R :=
    (Real.log_pos (by exact_mod_cast hR)).le
  have hB : 0 ≤ B := by
    unfold B
    exact mul_nonneg hE
      (add_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg hRlog smallKCandidateBound_nonneg))
        hE)
  have hpoint : ∀ r ∈ G, |I r - J r| ≤ B := by
    intro r hrMem
    have hrData := Finset.mem_filter.mp hrMem
    simpa [I, J, B] using
      (abs_sq_log_mul_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
        m (isMaynardDivisorTuple_of_mem_support hrData.1) hR hrData.2.2)
  rw [engelsmaS2CoordinateFiberGoodOuterMoment,
    engelsmaS2CoordinateFiberGoodComplementOuterMoment,
    ← Finset.sum_sub_distrib]
  change |∑ r ∈ G, (A r * I r - A r * J r)| ≤ _
  calc
    |∑ r ∈ G, (A r * I r - A r * J r)| =
        |∑ r ∈ G, A r * (I r - J r)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hrMem
      ring
    _ ≤ ∑ r ∈ G, |A r * (I r - J r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ G, A r * B := by
      apply Finset.sum_le_sum
      intro r hrMem
      rw [abs_mul, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_left (hpoint r hrMem)
          (maynardS2OuterSquarefreeAF_nonneg _ _)
      · exact maynardS2OuterSquarefreeAF_nonneg _ _
    _ = B * ∑ r ∈ G, A r := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ B * ∏ h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
      exact mul_le_mul_of_nonneg_left
        (engelsmaS2CoordinateFiberGoodOuterMass_le_faceBox R D m) hB

end BoundedGaps.Maynard
