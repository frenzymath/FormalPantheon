import BoundedGaps.Maynard.ConcreteS2EndpointIntegral
import BoundedGaps.Maynard.FaceDecomposition
import BoundedGaps.Maynard.VariationalNumeratorBridge

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable def engelsmaS2OffCoordinateLogFacePoint
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    maynardFaceIndex 105 (engelsmaIndexEquiv m) → ℝ :=
  fun j => Real.log (r (engelsmaIndexEquiv.symm j.1)) / Real.log R

noncomputable def engelsmaS2CoordinateFiberFaceIntegral
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1,
    smallKCandidate (maynardInsertCoordinate (engelsmaIndexEquiv m) x
      (engelsmaS2OffCoordinateLogFacePoint R m r))

theorem engelsmaS2CoordinateFiberPolynomialTest_eq_facePolynomial
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) (x : ℝ) :
    engelsmaS2CoordinateFiberPolynomialTest R m r x =
      smallKRealPolynomial
        (maynardInsertCoordinate (engelsmaIndexEquiv m) x
          (engelsmaS2OffCoordinateLogFacePoint R m r)) := by
  unfold engelsmaS2CoordinateFiberPolynomialTest
    maynardS2CoordinateFiberTest engelsmaSmallKPolynomial
  congr 1
  funext i
  by_cases hi : i = engelsmaIndexEquiv m
  · subst i
    simp [maynardInsertCoordinate]
  · have hne : engelsmaIndexEquiv.symm i ≠ m := by
      intro h
      apply hi
      simpa [h] using (engelsmaIndexEquiv.apply_symm_apply i).symm
    rw [maynardInsertCoordinate_off (engelsmaIndexEquiv m) x _ i hi]
    simp [Function.update, hne, engelsmaS2OffCoordinateLogFacePoint]

set_option maxRecDepth 4000 in
theorem engelsmaS2OffCoordinateLogFacePoint_mem_faceSimplex
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R) (hrm : r m = 1) :
    engelsmaS2OffCoordinateLogFacePoint R m r ∈
      maynardFaceSimplex (engelsmaIndexEquiv m) := by
  let t := engelsmaS2OffCoordinateLogFacePoint R m r
  let u : Fin 105 → ℝ := fun i =>
    normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R r
      (engelsmaIndexEquiv.symm i)
  have hu : u ∈ maynardSimplex 105 := by
    constructor
    · rw [maynardCube, maynardCubeOf, Set.mem_pi]
      intro i hi
      exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
        hR hr.mem_maynardDivisorTupleBox (engelsmaIndexEquiv.symm i)
    · have hsum : (∑ i : Fin 105, u i) =
          ∑ h : BoundedGaps.engelsmaTuple,
            normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R r h := by
        exact engelsmaIndexEquiv.symm.sum_comp _
      rw [hsum]
      exact ((divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
        hR (fun h => (mem_maynardDivisorTupleBox_iff.mp
          hr.mem_maynardDivisorTupleBox h).1)).mp hr.1).le
  have hinsert :
      maynardInsertCoordinate (engelsmaIndexEquiv m) 0 t = u := by
    funext i
    by_cases hi : i = engelsmaIndexEquiv m
    · subst i
      simp [u, normalizedDivisorLogTuple, hrm, maynardInsertCoordinate]
    · simp [u, t, normalizedDivisorLogTuple,
        engelsmaS2OffCoordinateLogFacePoint, maynardInsertCoordinate, hi]
  apply face_mem_of_insert_mem_simplex (engelsmaIndexEquiv m) 0 t
  rw [hinsert]
  exact hu

set_option maxRecDepth 4000 in
theorem sum_engelsmaS2OffCoordinateLogFacePoint_eq_log_product_div
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R) (hrm : r m = 1) :
    (∑ j, engelsmaS2OffCoordinateLogFacePoint R m r j) =
      Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R := by
  let t := engelsmaS2OffCoordinateLogFacePoint R m r
  let u : Fin 105 → ℝ := fun i =>
    normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R r
      (engelsmaIndexEquiv.symm i)
  have hinsert :
      maynardInsertCoordinate (engelsmaIndexEquiv m) 0 t = u := by
    funext i
    by_cases hi : i = engelsmaIndexEquiv m
    · subst i
      simp [u, normalizedDivisorLogTuple, hrm, maynardInsertCoordinate]
    · simp [u, t, normalizedDivisorLogTuple,
        engelsmaS2OffCoordinateLogFacePoint, maynardInsertCoordinate, hi]
  calc
    (∑ j, t j) = 0 + ∑ j, t j := by ring
    _ = ∑ i, maynardInsertCoordinate (engelsmaIndexEquiv m) 0 t i :=
      (sum_insertCoordinate (engelsmaIndexEquiv m) 0 t).symm
    _ = ∑ i, u i := by rw [hinsert]
    _ = ∑ h : BoundedGaps.engelsmaTuple,
        normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R r h :=
      engelsmaIndexEquiv.symm.sum_comp _
    _ = Real.log (divisorTupleProduct BoundedGaps.engelsmaTuple r) /
        Real.log R :=
      sum_normalizedDivisorLogTuple_eq_log_product_div hR
        (fun h => (mem_maynardDivisorTupleBox_iff.mp
          hr.mem_maynardDivisorTupleBox h).1)
    _ = Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R := by
      rw [divisorTupleProduct_eq_offCoordinateProduct m hrm]

set_option maxRecDepth 6000 in
theorem engelsmaS2CoordinateFiber_complementIntegral_eq_faceIntegral
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R) (hrm : r m = 1) :
    (∫ x in (0 : ℝ)..(
      1 - Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x) =
      engelsmaS2CoordinateFiberFaceIntegral R m r := by
  let mi := engelsmaIndexEquiv m
  let t := engelsmaS2OffCoordinateLogFacePoint R m r
  let c := 1 - ∑ j, t j
  have ht : t ∈ maynardFaceSimplex mi := by
    simpa [mi, t] using
      engelsmaS2OffCoordinateLogFacePoint_mem_faceSimplex m hr hR hrm
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr ht.2
    · exact sub_le_self _ (Finset.sum_nonneg fun j hj => ht.1 j)
  have hendpoint :
      1 - Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R = c := by
    rw [← sum_engelsmaS2OffCoordinateLogFacePoint_eq_log_product_div
      m hr hR hrm]
  rw [hendpoint]
  have hpoly : ∀ x ∈ Set.Icc (0 : ℝ) c,
      engelsmaS2CoordinateFiberPolynomialTest R m r x =
        smallKCandidate (maynardInsertCoordinate mi x t) := by
    intro x hx
    have hs := (insert_mem_simplex_iff mi x t ht).2 hx
    rw [engelsmaS2CoordinateFiberPolynomialTest_eq_facePolynomial]
    simp [smallKCandidate, hs, mi, t]
  have hshort :
      (∫ x in (0 : ℝ)..c,
        engelsmaS2CoordinateFiberPolynomialTest R m r x) =
        ∫ x in Set.Icc (0 : ℝ) c,
          smallKCandidate (maynardInsertCoordinate mi x t) := by
    rw [intervalIntegral.integral_of_le hc.1]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc hpoly
  rw [hshort]
  unfold engelsmaS2CoordinateFiberFaceIntegral
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Icc
  · exact Set.Icc_subset_Icc le_rfl hc.2
  · intro x hx
    have hxNot : x ∉ Set.Icc (0 : ℝ) c := hx.2
    have hs : maynardInsertCoordinate mi x t ∉ maynardSimplex 105 := by
      rw [insert_mem_simplex_iff mi x t ht]
      exact hxNot
    simp [smallKCandidate, hs, mi, t]

end BoundedGaps.Maynard
