import BoundedGaps.Maynard.ConcreteS2EndpointLog
import BoundedGaps.Maynard.ConcreteS2PolynomialBound
import BoundedGaps.Maynard.MaynardS2CoordinateFiberLocalSeries

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory Set

set_option maxRecDepth 5000 in
theorem abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    |(∫ x in (0 : ℝ)..(
        Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x) -
      ∫ x in (0 : ℝ)..(
        1 - Real.log (maynardS2OffCoordinateProduct
          BoundedGaps.engelsmaTuple m r) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x| ≤
      smallKCandidateBound * (Real.log 3 / Real.log R) := by
  let P := maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r
  let Q := maynardS2CoordinateFiberEndpoint R P
  let q : ℝ := Real.log Q / Real.log R
  let c : ℝ := 1 - Real.log P / Real.log R
  let G := engelsmaS2CoordinateFiberPolynomialTest R m r
  have hP : 0 < P := maynardS2OffCoordinateProduct_pos m r hr
  have hPlt : P < R := maynardS2OffCoordinateProduct_lt m r hr
  have hQnat : 1 < Q := by simpa [Q, P] using hQ
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hPlog : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  have hPlogLe : Real.log P ≤ Real.log R := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hP))
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hPlt.le)
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold c
      have : Real.log P / Real.log R ≤ 1 :=
        (div_le_iff₀ hRlog).2 (by linarith)
      linarith
    · unfold c
      exact sub_le_self _ (div_nonneg hPlog hRlog.le)
  have hQP : Q * P < R := by
    have hle : Q * P ≤ R - 1 := by
      unfold Q maynardS2CoordinateFiberEndpoint
      simpa [Nat.mul_comm] using Nat.mul_div_le (R - 1) P
    omega
  have hlogQP : Real.log Q + Real.log P ≤ Real.log R := by
    rw [← Real.log_mul (by exact_mod_cast (Nat.zero_lt_of_lt hQnat).ne')
      (by exact_mod_cast hP.ne')]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr
        (by exact_mod_cast Nat.mul_pos (Nat.zero_lt_of_lt hQnat) hP))
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hQP.le)
  have hqc : q ≤ c := by
    unfold q c
    calc
      Real.log Q / Real.log R ≤
          (Real.log R - Real.log P) / Real.log R :=
        div_le_div_of_nonneg_right (by linarith [hlogQP]) hRlog.le
      _ = 1 - Real.log P / Real.log R := by field_simp [hRlog.ne']
  have hq0 : 0 ≤ q := by
    unfold q
    exact div_nonneg (Real.log_pos (by exact_mod_cast hQnat)).le hRlog.le
  have hnorm : ∀ x ∈ Set.uIcc c q, ‖G x‖ ≤ smallKCandidateBound := by
    intro x hx
    rw [Set.uIcc_of_ge hqc] at hx
    apply engelsmaS2CoordinateFiberPolynomialTest_norm_le_of_cube R m r x
    intro h
    by_cases hhm : h = m
    · subst h
      simpa [G, Function.update] using
        (show x ∈ Set.Icc (0 : ℝ) 1 from
          ⟨hq0.trans hx.1, hx.2.trans hc.2⟩)
    · simpa [G, Function.update, hhm, normalizedDivisorLogTuple] using
        normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
          hR hr.mem_maynardDivisorTupleBox h
  have hGcont : Continuous G :=
    (contDiff_engelsmaS2CoordinateFiberPolynomialTest R m r).continuous
  have hqInt : IntervalIntegrable G volume 0 q := hGcont.intervalIntegrable _ _
  have hcInt : IntervalIntegrable G volume 0 c := hGcont.intervalIntegrable _ _
  have hshort := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hnorm x (Set.uIoc_subset_uIcc hx))
  have hgap : c - q ≤ Real.log 3 / Real.log R := by
    have habs :=
      abs_maynardS2CoordinateFiberEndpoint_log_ratio_sub_complement_log_ratio_le
        (m := m) (r := r) hr hR hQ
    change |q - c| ≤ Real.log 3 / Real.log R at habs
    rw [abs_of_nonpos (sub_nonpos.mpr hqc)] at habs
    linarith
  change |(∫ x in (0 : ℝ)..q, G x) - ∫ x in (0 : ℝ)..c, G x| ≤ _
  rw [intervalIntegral.integral_interval_sub_left hqInt hcInt]
  calc
    |∫ x in c..q, G x| = ‖∫ x in c..q, G x‖ := by rw [Real.norm_eq_abs]
    _ ≤ smallKCandidateBound * |q - c| := hshort
    _ = smallKCandidateBound * (c - q) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hqc)]
      ring
    _ ≤ smallKCandidateBound * (Real.log 3 / Real.log R) :=
      mul_le_mul_of_nonneg_left hgap smallKCandidateBound_nonneg

end BoundedGaps.Maynard
