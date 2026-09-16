import PrimesRestrictedDigits.BasicEstimates.StrictAbelSummation
import PrimesRestrictedDigits.BasicEstimates.PrimeCountingBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev

/-!
# Reciprocal primes from Chebyshev and Abel summation

These deliberately coarse absolute estimates suffice for the repaired proof of Maynard's Lemma
7.4 without importing a Mertens asymptotic.
-/

open scoped BigOperators
open MeasureTheory

namespace PrimesRestrictedDigits

/-- A convenient absolute Chebyshev bound for real cutoffs. -/
theorem realPrimeCounting_le_eight_mul_div_log
    {x : Real} (hx : 2 ≤ x) :
    realPrimeCounting x ≤ 8 * x / Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlogSqrt : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_sqrt hx0]
  have hlogLe : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx0
      (show (0 : Real) < 1 / 2 by norm_num)
    rw [show x ^ (1 / 2 : Real) = Real.sqrt x by
      exact (Real.sqrt_eq_rpow x).symm] at h
    nlinarith
  have hsqrtLe : Real.sqrt x ≤ 2 * x / Real.log x := by
    rw [le_div_iff₀ hlog]
    nlinarith [Real.sq_sqrt hx0]
  have hlogFour : Real.log 4 ≤ 3 := by
    exact (Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < 4)).trans_eq (by norm_num)
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  change realPrimeCounting x ≤ _ at hpi
  rw [hlogSqrt] at hpi
  calc
    realPrimeCounting x ≤
        Real.log 4 * x / (Real.log x / 2) + Real.sqrt x := hpi
    _ = 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by field_simp
    _ ≤ 6 * x / Real.log x + 2 * x / Real.log x := by
      gcongr
      nlinarith
    _ = 8 * x / Real.log x := by ring

private theorem integral_one_div_mul_log
    {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) =
      Real.log (Real.log b / Real.log a) := by
  have hb : 1 < b := ha.trans_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : Real ↦ Real.log (Real.log x))
        (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha.trans_le ht.1
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1)
    have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    convert (Real.hasDerivAt_log ht0).log hlog0 using 1; field_simp
  have hint : IntervalIntegrable (fun t : Real ↦ 1 / (t * Real.log t))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hlogCont : ContinuousOn Real.log (Set.uIcc a b) :=
      Real.continuousOn_log.mono (by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact Set.mem_compl_singleton_iff.mpr
          (ne_of_gt (zero_lt_one.trans (ha.trans_le ht.1))))
    exact continuousOn_const.div (continuousOn_id.mul hlogCont) (by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht1 : 1 < t := ha.trans_le ht.1
      exact mul_ne_zero (ne_of_gt (zero_lt_one.trans ht1))
        (ne_of_gt (Real.log_pos ht1)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (ne_of_gt (Real.log_pos hb))
      (ne_of_gt (Real.log_pos ha))]

private theorem intervalIntegrable_realPrimeCountingLt_div_sq
    {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ realPrimeCountingLt t / t ^ 2)
      volume a b := by
  have hweightCont : ContinuousOn (fun t : Real ↦ (t ^ 2)⁻¹)
      (Set.Icc a b) :=
    (continuousOn_id.pow 2).inv₀ (by
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hweight : IntegrableOn (fun t : Real ↦ (t ^ 2)⁻¹)
      (Set.Icc a b) := hweightCont.integrableOn_Icc
  have hm : AEStronglyMeasurable realPrimeCountingLt
      (volume.restrict (Set.Icc a b)) :=
    measurable_realPrimeCountingLt.aestronglyMeasurable
  let C : Real := realPrimeCountingLt b
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      ‖realPrimeCountingLt t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hceil : Nat.ceil t ≤ Nat.ceil b := Nat.ceil_mono ht.2
    have hcount : Nat.primeCounting' (Nat.ceil t) ≤
        Nat.primeCounting' (Nat.ceil b) := Nat.monotone_primeCounting' hceil
    rw [show realPrimeCountingLt t =
      (Nat.primeCounting' (Nat.ceil t) : Real) by rfl,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (Nat.primeCounting' (Nat.ceil t) : Real) ≤
      (Nat.primeCounting' (Nat.ceil b) : Real)
    exact_mod_cast hcount
  have htop : MemLp realPrimeCountingLt ⊤
      (volume.restrict (Set.Icc a b)) :=
    memLp_top_of_bound hm C hbound
  have hprod : Integrable
      (fun t ↦ realPrimeCountingLt t * (t ^ 2)⁻¹)
      (volume.restrict (Set.Icc a b)) :=
    hweight.mul_of_top_right htop
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  simpa [IntegrableOn, div_eq_mul_inv] using hprod

/-- Reciprocal-prime sum on the exact real half-open interval `[a,b)`. -/
theorem sum_prime_inv_halfOpen_le_chebyshev
    (a b : Real) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
      (p : Real)⁻¹) ≤
      8 / Real.log b + 8 * Real.log (Real.log b / Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := ha1.trans_le hab
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hfCont : ContinuousOn (fun t : Real ↦ t⁻¹) (Set.Icc a b) :=
    continuousOn_id.inv₀ (by
      intro t ht
      exact ne_of_gt (ha0.trans_le ht.1))
  have hfDiff : ∀ t ∈ Set.Ioo a b,
      DifferentiableAt Real (fun x : Real ↦ x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (ha0.trans_le ht.1.le))
  have hfInt : IntervalIntegrable
      (deriv fun x : Real ↦ x⁻¹) volume a b := by
    have hcont : ContinuousOn (fun t : Real ↦ -(t ^ 2)⁻¹)
        (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact ((continuousOn_id.pow 2).inv₀ (by
        intro t ht
        exact pow_ne_zero 2 (ne_of_gt (ha0.trans_le ht.1)))).neg
    have hi : IntervalIntegrable (fun t : Real ↦ -(t ^ 2)⁻¹)
        volume a b := hcont.intervalIntegrable
    convert hi using 1
    funext t
    exact deriv_inv
  have hAbel := sum_prime_halfOpen_eq_boundary_sub_integral
    (f := fun t : Real ↦ t⁻¹) hab hfCont hfDiff hfInt
  have hIntegral :
      (∫ t in a..b,
        deriv (fun x : Real ↦ x⁻¹) t * realPrimeCountingLt t) =
        -∫ t in a..b, realPrimeCountingLt t / t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change deriv (fun x : Real ↦ x⁻¹) t * realPrimeCountingLt t =
      -(realPrimeCountingLt t / t ^ 2)
    simp only [deriv_inv]
    ring
  rw [hIntegral] at hAbel
  have hcountB : realPrimeCountingLt b ≤ 8 * b / Real.log b :=
    (realPrimeCountingLt_le_realPrimeCounting b).trans
      (realPrimeCounting_le_eight_mul_div_log (by linarith))
  have hboundary : b⁻¹ * realPrimeCountingLt b ≤ 8 / Real.log b := by
    calc
      b⁻¹ * realPrimeCountingLt b ≤ b⁻¹ * (8 * b / Real.log b) := by
        gcongr
      _ = 8 / Real.log b := by field_simp
  have hlower : 0 ≤ a⁻¹ * realPrimeCountingLt a := by
    apply mul_nonneg (inv_nonneg.mpr ha0.le)
    change 0 ≤ (Nat.primeCounting' (Nat.ceil a) : Real)
    positivity
  have hgInt := intervalIntegrable_realPrimeCountingLt_div_sq ha0 hab
  have huInt : IntervalIntegrable (fun t : Real ↦ 8 / (t * Real.log t))
      volume a b := by
    have hcont : ContinuousOn (fun t : Real ↦ 8 / (t * Real.log t))
        (Set.uIcc a b) := by
      have hlogCont : ContinuousOn Real.log (Set.uIcc a b) :=
        Real.continuousOn_log.mono (by
          intro t ht
          rw [Set.uIcc_of_le hab] at ht
          exact Set.mem_compl_singleton_iff.mpr
            (ne_of_gt (ha0.trans_le ht.1)))
      exact continuousOn_const.div (continuousOn_id.mul hlogCont) (by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht1 : 1 < t := ha1.trans_le ht.1
        exact mul_ne_zero (ne_of_gt (ha0.trans_le ht.1))
          (ne_of_gt (Real.log_pos ht1)))
    exact hcont.intervalIntegrable
  have hIntegralLe :
      (∫ t in a..b, realPrimeCountingLt t / t ^ 2) ≤
        ∫ t in a..b, 8 / (t * Real.log t) := by
    apply intervalIntegral.integral_mono_on hab hgInt huInt
    intro t ht
    have ht2 : 2 ≤ t := ha.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hcount : realPrimeCountingLt t ≤ 8 * t / Real.log t :=
      (realPrimeCountingLt_le_realPrimeCounting t).trans
        (realPrimeCounting_le_eight_mul_div_log ht2)
    calc
      realPrimeCountingLt t / t ^ 2 ≤ (8 * t / Real.log t) / t ^ 2 := by
        exact div_le_div_of_nonneg_right hcount (sq_nonneg t)
      _ = 8 / (t * Real.log t) := by field_simp
  have hUpperEval :
      (∫ t in a..b, 8 / (t * Real.log t)) =
        8 * Real.log (Real.log b / Real.log a) := by
    rw [show (fun t : Real ↦ 8 / (t * Real.log t)) =
        fun t ↦ 8 * (1 / (t * Real.log t)) by funext t; ring,
      intervalIntegral.integral_const_mul,
      integral_one_div_mul_log ha1 hab]
  rw [hAbel]
  calc
    b⁻¹ * realPrimeCountingLt b - a⁻¹ * realPrimeCountingLt a -
        -∫ t in a..b, realPrimeCountingLt t / t ^ 2 ≤
      b⁻¹ * realPrimeCountingLt b +
        ∫ t in a..b, realPrimeCountingLt t / t ^ 2 := by linarith
    _ ≤ 8 / Real.log b + ∫ t in a..b, 8 / (t * Real.log t) :=
      add_le_add hboundary hIntegralLe
    _ = 8 / Real.log b +
        8 * Real.log (Real.log b / Real.log a) := by
      rw [hUpperEval]

/-- The inverse reciprocal-prime factor is bounded by its linear majorant. -/
theorem inverse_one_sub_prime_inv_le
    {p : Nat} (hp : 2 ≤ p) :
    (1 - (p : Real)⁻¹)⁻¹ ≤ 1 + 2 * (p : Real)⁻¹ := by
  have hpReal : (2 : Real) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : Real) < p := by linarith
  have hpSub : (0 : Real) < p - 1 := by linarith
  rw [show (1 - (p : Real)⁻¹)⁻¹ = (p : Real) / (p - 1) by
    field_simp]
  rw [div_le_iff₀ hpSub]
  rw [show (1 + 2 * (p : Real)⁻¹) * (p - 1) =
    p + (p - 2) / p by field_simp; ring]
  have : 0 ≤ ((p : Real) - 2) / p :=
    div_nonneg (by linarith) hp0.le
  linarith

/-- Inverse prime-product estimate on the exact half-open interval `[z,Y)`. -/
theorem intervalPrimeInverseProduct_le
    (z Y : Real) (hz : 2 ≤ z) (hzY : z ≤ Y) :
    (∏ p ∈ (naturalLeftClosedRightOpenInterval z Y).filter Nat.Prime,
      (1 - (p : Real)⁻¹)⁻¹) ≤
      Real.exp (16 / Real.log 2) *
        (Real.log Y / Real.log z) ^ (16 : Nat) := by
  let S := (naturalLeftClosedRightOpenInterval z Y).filter Nat.Prime
  have hz1 : 1 < z := by linarith
  have hY1 : 1 < Y := hz1.trans_le hzY
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hratio : 0 < Real.log Y / Real.log z := div_pos hlogY hlogz
  have hsum := sum_prime_inv_halfOpen_le_chebyshev z Y hz hzY
  have hprod :
      (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) ≤
        Real.exp (2 * ∑ p ∈ S, (p : Real)⁻¹) := by
    calc
      (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) ≤
          ∏ p ∈ S, (1 + 2 * (p : Real)⁻¹) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpPrime := (Finset.mem_filter.mp hp).2
          have hpReal : (1 : Real) < p := by
            exact_mod_cast hpPrime.one_lt
          exact inv_nonneg.mpr
            (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpReal)).le
        · intro p hp
          have hpInterval := mem_naturalLeftClosedRightOpenInterval.mp
            (Finset.mem_filter.mp hp).1
          have hpTwo : 2 ≤ p := by exact_mod_cast hz.trans hpInterval.1
          exact inverse_one_sub_prime_inv_le hpTwo
      _ ≤ Real.exp (∑ p ∈ S, 2 * (p : Real)⁻¹) :=
        Real.prod_one_add_le_exp_sum S (fun p ↦ by positivity)
      _ = Real.exp (2 * ∑ p ∈ S, (p : Real)⁻¹) := by
        rw [Finset.mul_sum]
  calc
    (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) ≤
        Real.exp (2 * ∑ p ∈ S, (p : Real)⁻¹) := hprod
    _ ≤ Real.exp
        (2 * (8 / Real.log Y +
          8 * Real.log (Real.log Y / Real.log z))) := by
      apply Real.exp_le_exp.mpr
      gcongr
    _ = Real.exp (16 / Real.log Y) *
        (Real.log Y / Real.log z) ^ (16 : Nat) := by
      rw [show 2 * (8 / Real.log Y +
          8 * Real.log (Real.log Y / Real.log z)) =
        16 / Real.log Y +
          16 * Real.log (Real.log Y / Real.log z) by ring,
        Real.exp_add]
      congr 1
      calc
        Real.exp (16 * Real.log (Real.log Y / Real.log z)) =
            Real.exp (Real.log (Real.log Y / Real.log z)) ^
              (16 : Nat) := by
          simpa using Real.exp_nat_mul
            (Real.log (Real.log Y / Real.log z)) 16
        _ = (Real.log Y / Real.log z) ^ (16 : Nat) := by
          rw [Real.exp_log hratio]
    _ ≤ Real.exp (16 / Real.log 2) *
        (Real.log Y / Real.log z) ^ (16 : Nat) := by
      have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogTwoLe : Real.log 2 ≤ Real.log Y :=
        Real.log_le_log (by norm_num) (hz.trans hzY)
      apply mul_le_mul_of_nonneg_right
      · apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 16)
          hlogTwo hlogTwoLe
      · positivity

end PrimesRestrictedDigits
