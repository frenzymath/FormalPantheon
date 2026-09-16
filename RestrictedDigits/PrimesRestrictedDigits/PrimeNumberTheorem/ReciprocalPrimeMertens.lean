import PrimesRestrictedDigits.BasicEstimates.LogarithmicIntegral
import PrimesRestrictedDigits.PrimeNumberTheorem.PrimeCountingLogSquare
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A sharp reciprocal-prime interval bound

Strict Abel summation and the completed log-square PNT give the exponent-one input for
`IWANIEC-ROSSER-SIEVE-1980`, Eq. (1.3), p. 171.
-/

open Finset MeasureTheory Set
open scoped BigOperators Topology

namespace PrimesRestrictedDigits

noncomputable section

private theorem integral_one_div_mul_log_sq {a b : Real}
    (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t ^ 2)) =
      1 / Real.log a - 1 / Real.log b := by
  have hcont : ContinuousOn (-Real.log⁻¹) (Set.Icc a b) := by
    have hlog : ContinuousOn Real.log (Set.Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
    exact (hlog.inv₀ (by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ha, ht.1])))).neg
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (-Real.log⁻¹)
        (1 / (t * Real.log t ^ 2)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ha, ht.1])
    have hlog0 : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))
    have hd := ((Real.hasDerivAt_log ht0).inv hlog0).neg
    apply hd.congr_deriv
    symm
    exact (by field_simp [ht0, hlog0])
  have hint : IntervalIntegrable
      (fun t : Real ↦ 1 / (t * Real.log t ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hlog : ContinuousOn Real.log (Set.Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
    apply continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
    intro t ht
    change t * Real.log t ^ 2 ≠ 0
    exact mul_ne_zero (ne_of_gt (by linarith [ha, ht.1]))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab hcont hderiv hint]
  simp only [Pi.neg_apply, Pi.inv_apply]
  ring

private theorem abs_integral_primeRemainder_div_sq_le
    {C a b : Real} (hC : 0 < C) (ha : 2 ≤ a) (hab : a ≤ b)
    (hPNT : ∀ x : Real, 2 ≤ x →
      |primeRemainder x| ≤ C * x / Real.log x ^ 2) :
    |∫ t in a..b, primeRemainder t / t ^ 2| ≤ C / Real.log a := by
  have ha1 : 1 < a := by linarith
  have hboundInt : IntervalIntegrable
      (fun t : Real ↦ C / (t * Real.log t ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hlog : ContinuousOn Real.log (Set.Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
    apply continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
    intro t ht
    change t * Real.log t ^ 2 ≠ 0
    exact mul_ne_zero (ne_of_gt (by linarith [ha, ht.1]))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : Real ↦ primeRemainder t / t ^ 2)
    (g := fun t : Real ↦ C / (t * Real.log t ^ 2)) hab (by
      filter_upwards [] with t
      intro htIoc
      have ht2 : 2 ≤ t := ha.trans htIoc.1.le
      have ht0 : 0 < t := by linarith
      have hlog0 : 0 < Real.log t := Real.log_pos (by linarith)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
      calc
        |primeRemainder t| / t ^ 2 ≤
            (C * t / Real.log t ^ 2) / t ^ 2 := by
          gcongr
          exact hPNT t ht2
        _ = C / (t * Real.log t ^ 2) := by field_simp) hboundInt
  rw [show (∫ t in a..b, C / (t * Real.log t ^ 2)) =
      C * (1 / Real.log a - 1 / Real.log b) by
    rw [show (fun t : Real ↦ C / (t * Real.log t ^ 2)) =
        fun t ↦ C * (1 / (t * Real.log t ^ 2)) by funext t; ring,
      intervalIntegral.integral_const_mul,
      integral_one_div_mul_log_sq ha1 hab]] at hnorm
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hdiff : 1 / Real.log a - 1 / Real.log b ≤ 1 / Real.log a := by
    have : 0 ≤ 1 / Real.log b := by positivity
    linarith
  rw [Real.norm_eq_abs] at hnorm
  simpa only [div_eq_mul_inv, one_mul] using
    hnorm.trans (mul_le_mul_of_nonneg_left hdiff hC.le)

private theorem strictRemainder_boundary_le
    {C t : Real} (hC : 0 < C) (ht : 2 ≤ t)
    (hPNT : |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |t⁻¹ * strictPrimeRemainder t| ≤
      C / Real.log t ^ 2 + 1 / t := by
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 < Real.log t := Real.log_pos (by linarith)
  have hs : |strictPrimeRemainder t| ≤ |primeRemainder t| + 1 := by
    calc
      |strictPrimeRemainder t| =
          |(strictPrimeRemainder t - primeRemainder t) +
            primeRemainder t| := by
        congr 1
        ring
      _ ≤ |strictPrimeRemainder t - primeRemainder t| +
          |primeRemainder t| := abs_add_le _ _
      _ ≤ 1 + |primeRemainder t| := by
        gcongr
        exact abs_strictPrimeRemainder_sub_primeRemainder_le_one t
      _ = |primeRemainder t| + 1 := by ring
  rw [abs_mul, abs_of_pos (inv_pos.mpr ht0)]
  calc
    t⁻¹ * |strictPrimeRemainder t| ≤
        t⁻¹ * (C * t / Real.log t ^ 2 + 1) := by
      exact mul_le_mul_of_nonneg_left
        (hs.trans (by simpa [add_comm] using add_le_add_right hPNT 1))
        (inv_nonneg.mpr ht0.le)
    _ = C / Real.log t ^ 2 + 1 / t := by field_simp

private theorem integral_one_div_mul_log {a b : Real}
    (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) =
      Real.log (Real.log b / Real.log a) := by
  have hb : 1 < b := ha.trans_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : Real ↦ Real.log (Real.log x))
        (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha.trans_le ht.1
    convert (Real.hasDerivAt_log
      (ne_of_gt (zero_lt_one.trans ht1))).log
        (ne_of_gt (Real.log_pos ht1)) using 1
    field_simp
  have hint : IntervalIntegrable
      (fun t : Real ↦ 1 / (t * Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hlog : ContinuousOn Real.log (Set.uIcc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ne_of_gt (zero_lt_one.trans (ha.trans_le ht.1))
    apply continuousOn_const.div (continuousOn_id.mul hlog)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (ha.trans_le ht.1)))
      (ne_of_gt (Real.log_pos (ha.trans_le ht.1)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (ne_of_gt (Real.log_pos hb))
      (ne_of_gt (Real.log_pos ha))]

private theorem sum_prime_inv_halfOpen_le_log_ratio_of_pnt
    {C w z : Real} (hC : 0 < C) (hw : 2 ≤ w) (hwz : w ≤ z)
    (hPNT : ∀ x : Real, 2 ≤ x →
      |primeRemainder x| ≤ C * x / Real.log x ^ 2) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
      (p : Real)⁻¹) ≤
      Real.log (Real.log z / Real.log w) +
        (C + 2 * C / Real.log 2 + 2) / Real.log w := by
  have hw0 : 0 < w := by linarith
  have hz0 : 0 < z := hw0.trans_le hwz
  have hw1 : 1 < w := by linarith
  have hz1 : 1 < z := hw1.trans_le hwz
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hcont : ContinuousOn (fun t : Real ↦ t⁻¹) (Set.Icc w z) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (hw0.trans_le ht.1))
  have hdiff : ∀ t ∈ Set.Ioo w z,
      DifferentiableAt Real (fun x : Real ↦ x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (hw0.trans_le ht.1.le))
  have hint : IntervalIntegrable
      (deriv fun x : Real ↦ x⁻¹) volume w z := by
    have hc : ContinuousOn (fun t : Real ↦ -(t ^ 2)⁻¹)
        (Set.uIcc w z) := by
      rw [Set.uIcc_of_le hwz]
      exact ((continuousOn_id.pow 2).inv₀ (fun t ht ↦
        pow_ne_zero 2 (ne_of_gt (hw0.trans_le ht.1)))).neg
    have hi : IntervalIntegrable (fun t : Real ↦ -(t ^ 2)⁻¹)
        volume w z := hc.intervalIntegrable
    convert hi using 1
    funext t
    exact deriv_inv
  have hdecomp := sum_prime_halfOpen_eq_main_add_remainders
    (f := fun t : Real ↦ t⁻¹) hw1 hwz hcont hdiff hint
  have hmain : (∫ t in w..z, t⁻¹ / Real.log t) =
      Real.log (Real.log z / Real.log w) := by
    convert integral_one_div_mul_log hw1 hwz using 1
    ring_nf
  have hBw := strictRemainder_boundary_le hC hw (hPNT w hw)
  have hBz := strictRemainder_boundary_le hC (hw.trans hwz)
    (hPNT z (hw.trans hwz))
  have hInt := abs_integral_primeRemainder_div_sq_le hC hw hwz hPNT
  have hderivInt :
      |∫ t in w..z,
        deriv (fun x : Real ↦ x⁻¹) t * primeRemainder t| ≤
          C / Real.log w := by
    have heq : (∫ t in w..z,
        deriv (fun x : Real ↦ x⁻¹) t * primeRemainder t) =
        -∫ t in w..z, primeRemainder t / t ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [deriv_inv]
      ring
    rw [heq, abs_neg]
    exact hInt
  have hraw :
      (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
        (p : Real)⁻¹) ≤
        Real.log (Real.log z / Real.log w) +
          (C / Real.log z ^ 2 + 1 / z) +
          (C / Real.log w ^ 2 + 1 / w) + C / Real.log w := by
    rw [hdecomp, hmain]
    calc
      Real.log (Real.log z / Real.log w) +
          z⁻¹ * strictPrimeRemainder z -
          w⁻¹ * strictPrimeRemainder w -
          (∫ t in w..z,
            deriv (fun x : Real ↦ x⁻¹) t * primeRemainder t) ≤
        Real.log (Real.log z / Real.log w) +
          |z⁻¹ * strictPrimeRemainder z| +
          |w⁻¹ * strictPrimeRemainder w| +
          |∫ t in w..z,
            deriv (fun x : Real ↦ x⁻¹) t * primeRemainder t| := by
        linarith [le_abs_self (z⁻¹ * strictPrimeRemainder z),
          neg_le_abs (w⁻¹ * strictPrimeRemainder w),
          neg_le_abs (∫ t in w..z,
            deriv (fun x : Real ↦ x⁻¹) t * primeRemainder t)]
      _ ≤ _ := by gcongr
  have hlogMono : Real.log w ≤ Real.log z := Real.log_le_log hw0 hwz
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoLe : Real.log 2 ≤ Real.log w :=
    Real.log_le_log (by norm_num) hw
  have hinvlogSqZ : 1 / Real.log z ^ 2 ≤
      (1 / Real.log 2) / Real.log w := by
    rw [div_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogz)
      (mul_pos hlogTwo hlogw)).mpr
    nlinarith [mul_self_le_mul_self hlogw.le hlogMono]
  have hinvlogSqW : 1 / Real.log w ^ 2 ≤
      (1 / Real.log 2) / Real.log w := by
    rw [div_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogw)
      (mul_pos hlogTwo hlogw)).mpr
    nlinarith
  have hinvZ : 1 / z ≤ 1 / Real.log w := by
    apply one_div_le_one_div_of_le hlogw
    exact (Real.log_le_sub_one_of_pos hw0).trans (by linarith)
  have hinvW : 1 / w ≤ 1 / Real.log w := by
    apply one_div_le_one_div_of_le hlogw
    exact (Real.log_le_sub_one_of_pos hw0).trans (by linarith)
  have hCz : C / Real.log z ^ 2 ≤
      C * ((1 / Real.log 2) / Real.log w) := by
    calc
      C / Real.log z ^ 2 = C * (1 / Real.log z ^ 2) := by ring
      _ ≤ C * ((1 / Real.log 2) / Real.log w) :=
        mul_le_mul_of_nonneg_left hinvlogSqZ hC.le
  have hCw : C / Real.log w ^ 2 ≤
      C * ((1 / Real.log 2) / Real.log w) := by
    calc
      C / Real.log w ^ 2 = C * (1 / Real.log w ^ 2) := by ring
      _ ≤ C * ((1 / Real.log 2) / Real.log w) :=
        mul_le_mul_of_nonneg_left hinvlogSqW hC.le
  have herr :
      C / Real.log z ^ 2 + 1 / z +
          (C / Real.log w ^ 2 + 1 / w) + C / Real.log w ≤
        C * ((1 / Real.log 2) / Real.log w) + 1 / Real.log w +
          (C * ((1 / Real.log 2) / Real.log w) + 1 / Real.log w) +
          C / Real.log w := by
    gcongr
  have herr' :
      C / Real.log z ^ 2 + 1 / z +
          (C / Real.log w ^ 2 + 1 / w) + C / Real.log w ≤
        (C + 2 * C / Real.log 2 + 2) / Real.log w := by
    calc
      _ ≤ _ := herr
      _ = _ := by ring
  linarith

/-- A uniform exponent-one reciprocal-prime estimate on the exact half-open
interval `[w,z)`. -/
theorem exists_sum_prime_inv_halfOpen_le_log_ratio :
    ∃ D : Real, 0 < D ∧ ∀ w z : Real, 2 ≤ w → w ≤ z →
      (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
        (p : Real)⁻¹) ≤
        Real.log (Real.log z / Real.log w) + D / Real.log w := by
  obtain ⟨C, hC, hPNT⟩ := primeCounting_log_sq_error
  let D : Real := C + 2 * C / Real.log 2 + 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < 2 * C / Real.log 2 :=
      div_pos (mul_pos (by norm_num) hC) hlogTwo
    linarith
  refine ⟨D, hD, ?_⟩
  intro w z hw hwz
  simpa [D] using
    sum_prime_inv_halfOpen_le_log_ratio_of_pnt hC hw hwz hPNT

end

end PrimesRestrictedDigits
