import BoundedGaps.Maynard.MaynardS2CoordinateFiberPolynomial

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory Set

theorem engelsmaS2CoordinateFiberPolynomialTest_norm_le_of_cube
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) (x : ℝ)
    (hx : ∀ h : BoundedGaps.engelsmaTuple,
      (Function.update (fun h => Real.log (r h) / Real.log R) m x) h ∈
        Set.Icc (0 : ℝ) 1) :
    ‖engelsmaS2CoordinateFiberPolynomialTest R m r x‖ ≤
      smallKCandidateBound := by
  unfold engelsmaS2CoordinateFiberPolynomialTest
    maynardS2CoordinateFiberTest engelsmaSmallKPolynomial
  apply smallKRealPolynomial_norm_le
  rw [maynardCube, maynardCubeOf, Set.mem_pi]
  intro i hi
  exact hx (engelsmaIndexEquiv.symm i)

set_option maxRecDepth 4000 in
theorem engelsmaS2CoordinateFiberPolynomialTest_mem_cube_on_endpoint_interval
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    ∀ x ∈ Set.uIcc (0 : ℝ)
      (Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
        Real.log R),
      ∀ h : BoundedGaps.engelsmaTuple,
        (Function.update (fun h => Real.log (r h) / Real.log R) m x) h ∈
          Set.Icc (0 : ℝ) 1 := by
  intro x hx h
  have hbox := hr.mem_maynardDivisorTupleBox
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hQreal : (1 : ℝ) <
      maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) := by
    exact_mod_cast hQ
  have hQlog : 0 < Real.log
      (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :=
    Real.log_pos hQreal
  have hP : 0 < maynardS2OffCoordinateProduct
      BoundedGaps.engelsmaTuple m r :=
    maynardS2OffCoordinateProduct_pos m r hr
  have hQle : maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) ≤ R := by
    unfold maynardS2CoordinateFiberEndpoint
    exact (Nat.div_le_self _ _).trans (by omega)
  have hQlogLe : Real.log
      (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
      Real.log R ≤ 1 := by
    apply (div_le_iff₀ hRlog).2
    have hQposReal : (0 : ℝ) <
        maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) := by
      exact_mod_cast (Nat.zero_lt_of_lt hQ)
    have hRposReal : (0 : ℝ) < R := by
      exact_mod_cast (Nat.zero_lt_of_lt hR)
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hQposReal) (Set.mem_Ioi.mpr hRposReal)
        (by exact_mod_cast hQle)
    linarith
  have hxIcc : x ∈ Set.Icc (0 : ℝ)
      (Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
        Real.log R) := by
    rw [Set.uIcc_of_le (div_nonneg hQlog.le hRlog.le)] at hx
    exact hx
  by_cases hhm : h = m
  · subst h
    simpa [Function.update] using
      (show x ∈ Set.Icc (0 : ℝ) 1 from
        ⟨hxIcc.1, hxIcc.2.trans hQlogLe⟩)
  · simpa [Function.update, hhm, normalizedDivisorLogTuple] using
      normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
        hR hbox h

set_option maxRecDepth 4000 in
theorem engelsmaS2CoordinateFiberPolynomialTest_norm_le_on_endpoint_interval
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    ∀ x ∈ Set.uIcc (0 : ℝ)
      (Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
        Real.log R),
      ‖engelsmaS2CoordinateFiberPolynomialTest R m r x‖ ≤
        smallKCandidateBound := by
  intro x hx
  exact engelsmaS2CoordinateFiberPolynomialTest_norm_le_of_cube R m r x
    (engelsmaS2CoordinateFiberPolynomialTest_mem_cube_on_endpoint_interval
      (m := m) (r := r) hr hR hQ x hx)

set_option maxRecDepth 4000 in
theorem norm_engelsmaS2CoordinateFiberPolynomialTest_intervalIntegral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    ‖∫ x in (0 : ℝ)..(
      Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
        Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x‖ ≤
      smallKCandidateBound *
        (Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
          Real.log R) := by
  let Q : ℕ := maynardS2CoordinateFiberEndpoint R
    (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hQlog : 0 ≤ Real.log Q := (Real.log_pos hQreal).le
  have hb : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg hQlog hRlog.le
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => engelsmaS2CoordinateFiberPolynomialTest_norm_le_on_endpoint_interval
      (m := m) (r := r) hr hR hQ x (Set.uIoc_subset_uIcc hx))
  simpa [Q, Real.norm_eq_abs, abs_of_nonneg hb, sub_zero] using hnorm

set_option maxRecDepth 5000 in
theorem sq_log_mul_engelsmaS2CoordinateFiberPolynomialTest_intervalIntegral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    ((Real.log R) *
      (∫ x in (0 : ℝ)..(
        Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
          Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 ≤
      (Real.log R * smallKCandidateBound) ^ 2 := by
  let Q : ℕ := maynardS2CoordinateFiberEndpoint R
    (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let I : ℝ := ∫ x in (0 : ℝ)..(Real.log Q / Real.log R),
    engelsmaS2CoordinateFiberPolynomialTest R m r x
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hQlog : 0 ≤ Real.log Q := (Real.log_pos hQreal).le
  have hratio_nonneg : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg hQlog hRlog.le
  have hQle : Q ≤ R := by
    unfold Q maynardS2CoordinateFiberEndpoint
    exact (Nat.div_le_self _ _).trans (by omega)
  have hratio_le_one : Real.log Q / Real.log R ≤ 1 := by
    apply (div_le_iff₀ hRlog).2
    have hQposReal : (0 : ℝ) < Q := by
      exact_mod_cast (Nat.zero_lt_of_lt hQ)
    have hRposReal : (0 : ℝ) < R := by
      exact_mod_cast (Nat.zero_lt_of_lt hR)
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hQposReal) (Set.mem_Ioi.mpr hRposReal)
        (by exact_mod_cast hQle)
    linarith
  have hIabs : |I| ≤ smallKCandidateBound := by
    have hI := norm_engelsmaS2CoordinateFiberPolynomialTest_intervalIntegral_le
      (m := m) (r := r) hr hR hQ
    have hI' : ‖I‖ ≤ smallKCandidateBound *
        (Real.log Q / Real.log R) := by
      simpa [I] using hI
    calc
      |I| = ‖I‖ := by rw [Real.norm_eq_abs]
      _ ≤ smallKCandidateBound * (Real.log Q / Real.log R) := hI'
      _ ≤ smallKCandidateBound * 1 :=
        mul_le_mul_of_nonneg_left hratio_le_one smallKCandidateBound_nonneg
      _ = smallKCandidateBound := by ring
  have hlogNonneg : 0 ≤ Real.log R := hRlog.le
  have hprod : |Real.log R * I| ≤ Real.log R * smallKCandidateBound := by
    rw [abs_mul, abs_of_nonneg hlogNonneg]
    exact mul_le_mul_of_nonneg_left hIabs hlogNonneg
  have hprodNonneg : 0 ≤ Real.log R * smallKCandidateBound := by
    exact mul_nonneg hlogNonneg smallKCandidateBound_nonneg
  have hsquare : |Real.log R * I| ^ 2 ≤
      (Real.log R * smallKCandidateBound) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hprodNonneg).2 hprod
  change (Real.log R * I) ^ 2 ≤
    (Real.log R * smallKCandidateBound) ^ 2
  simpa only [sq_abs] using hsquare

end BoundedGaps.Maynard
