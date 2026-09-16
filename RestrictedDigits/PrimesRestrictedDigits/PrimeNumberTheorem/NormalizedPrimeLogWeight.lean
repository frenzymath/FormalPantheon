import PrimesRestrictedDigits.PrimeNumberTheorem.PrimeCountingLogSquare
import PrimesRestrictedDigits.SieveDecomposition.BuchstabIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Normalized logarithmic prime weights

Strict Abel summation and the log-square prime number theorem show that the
weighted primes in `(X^a, X^b]` have limiting mass `b-a`.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators Topology

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def normalizedPrimeLogWeight (X p : Nat) : Real :=
  Real.log (p : Real) / ((p : Real) * Real.log (X : Real))

namespace NormalizedPrimeLogWeight

noncomputable def realWeight (X t : Real) : Real :=
  Real.log t / (t * Real.log X)

private theorem realWeight_hasDerivAt {X t : Real}
    (ht : t ≠ 0) (hXlog : Real.log X ≠ 0) :
    HasDerivAt (realWeight X)
      ((1 - Real.log t) / (t ^ 2 * Real.log X)) t := by
  unfold realWeight
  have hden : t * Real.log X ≠ 0 := mul_ne_zero ht hXlog
  have hd := (Real.hasDerivAt_log ht).div
      ((hasDerivAt_id t).mul_const (Real.log X)) hden
  apply hd.congr_deriv
  simp only [id_eq]
  field_simp [ht, hXlog]

private theorem realWeight_deriv {X t : Real}
    (ht : t ≠ 0) (hXlog : Real.log X ≠ 0) :
    deriv (realWeight X) t =
      (1 - Real.log t) / (t ^ 2 * Real.log X) :=
  (realWeight_hasDerivAt ht hXlog).deriv

private theorem integral_one_div_mul_log {a b : Real}
    (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) = Real.log (Real.log b / Real.log a) := by
  have hb : 1 < b := ha.trans_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : Real => Real.log (Real.log x))
        (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha.trans_le ht.1
    convert (Real.hasDerivAt_log
      (ne_of_gt (zero_lt_one.trans ht1))).log
        (ne_of_gt (Real.log_pos ht1)) using 1
    field_simp
  have hint : IntervalIntegrable
      (fun t : Real => 1 / (t * Real.log t)) volume a b := by
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

private theorem realWeight_boundary_le
    {C X t : Real} (hC : 0 < C) (hX : 1 < X) (ht : 2 ≤ t)
    (hPNT : |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |realWeight X t * strictPrimeRemainder t| ≤
      C / (Real.log X * Real.log t) + Real.log t / (t * Real.log X) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hs : |strictPrimeRemainder t| ≤ |primeRemainder t| + 1 := by
    calc
      |strictPrimeRemainder t| =
          |(strictPrimeRemainder t - primeRemainder t) +
            primeRemainder t| := by congr 1; ring
      _ ≤ |strictPrimeRemainder t - primeRemainder t| +
          |primeRemainder t| := abs_add_le _ _
      _ ≤ 1 + |primeRemainder t| := by
        gcongr
        exact abs_strictPrimeRemainder_sub_primeRemainder_le_one t
      _ = |primeRemainder t| + 1 := by ring
  rw [abs_mul, abs_of_pos (show 0 < realWeight X t by
    unfold realWeight
    positivity)]
  calc
    realWeight X t * |strictPrimeRemainder t| ≤
        realWeight X t * (C * t / Real.log t ^ 2 + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (by
        unfold realWeight
        positivity))
      linarith [hs, hPNT]
    _ = C / (Real.log X * Real.log t) +
        Real.log t / (t * Real.log X) := by
      unfold realWeight
      field_simp [ne_of_gt ht0, ne_of_gt hlogt, ne_of_gt hlogX]

private theorem realWeight_remainderIntegral_le
    {C X a b : Real} (hC : 0 < C) (hX : 1 < X) (ha : Real.exp 1 ≤ a)
    (hab : a ≤ b) (hPNT : ∀ t : Real, 2 ≤ t ->
      |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |∫ t in a..b, deriv (realWeight X) t * primeRemainder t| ≤
      C / Real.log X * Real.log (Real.log b / Real.log a) := by
  have ha1 : 1 < a := by
    linarith [Real.exp_one_gt_d9]
  have ha2 : 2 ≤ a := by
    linarith [Real.exp_one_gt_d9]
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hboundInt : IntervalIntegrable
      (fun t : Real => C / Real.log X * (1 / (t * Real.log t)))
      volume a b := by
    exact (ContinuousOn.intervalIntegrable_of_Icc hab (by
      have hlog : ContinuousOn Real.log (Set.Icc a b) := by
        apply Real.continuousOn_log.mono
        intro t ht
        exact ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
      exact continuousOn_const.mul
        (continuousOn_const.div (continuousOn_id.mul hlog) (by
          intro t ht
          exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1)))
            (ne_of_gt (Real.log_pos (ha1.trans_le ht.1)))))))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : Real => deriv (realWeight X) t * primeRemainder t)
    (g := fun t : Real => C / Real.log X * (1 / (t * Real.log t)))
    hab (by
      filter_upwards [] with t
      intro htIoc
      have ht0 : 0 < t := zero_lt_one.trans (ha1.trans_le htIoc.1.le)
      have ht1 : 1 < t := ha1.trans_le htIoc.1.le
      have ht2 : 2 ≤ t := ha2.trans htIoc.1.le
      have hlogt : 1 ≤ Real.log t := by
        exact (Real.le_log_iff_exp_le ht0).2 (ha.trans htIoc.1.le)
      rw [realWeight_deriv (ne_of_gt ht0) (ne_of_gt hlogX),
        Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
        abs_of_pos (sq_pos_of_pos ht0), abs_of_pos hlogX]
      calc
        |1 - Real.log t| / (t ^ 2 * Real.log X) * |primeRemainder t| ≤
            |1 - Real.log t| / (t ^ 2 * Real.log X) *
              (C * t / Real.log t ^ 2) := by
          gcongr
          exact hPNT t ht2
        _ ≤ C / Real.log X * (1 / (t * Real.log t)) := by
          have habs : |1 - Real.log t| ≤ Real.log t := by
            rw [abs_of_nonpos (by linarith)]
            linarith
          have hden : 0 < t ^ 2 * Real.log X :=
            mul_pos (sq_pos_of_pos ht0) hlogX
          have hfac : 0 ≤ C * t / Real.log t ^ 2 := by positivity
          calc
            |1 - Real.log t| / (t ^ 2 * Real.log X) *
                (C * t / Real.log t ^ 2) ≤
                Real.log t / (t ^ 2 * Real.log X) *
                  (C * t / Real.log t ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_right habs hden.le) hfac
            _ = C / Real.log X * (1 / (t * Real.log t)) := by
              field_simp [ne_of_gt ht0, ne_of_gt (Real.log_pos ht1),
                ne_of_gt hlogX]
              )
      hboundInt
  rw [show (∫ t in a..b,
      C / Real.log X * (1 / (t * Real.log t))) =
      C / Real.log X * Real.log (Real.log b / Real.log a) by
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_mul_log ha1 hab]] at hnorm
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogab : Real.log a ≤ Real.log b :=
    Real.log_le_log (zero_lt_one.trans ha1) hab
  have hratio : 1 ≤ Real.log b / Real.log a :=
    (le_div_iff₀ hloga).2 (by simpa using hlogab)
  have hlogRatio : 0 ≤ Real.log (Real.log b / Real.log a) :=
    Real.log_nonneg hratio
  simpa [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (div_nonneg hC.le hlogX.le) hlogRatio)] using hnorm

private theorem realWeight_halfOpen_error_le
    {C X a b : Real} (hC : 0 < C) (hX : 1 < X) (ha : Real.exp 1 ≤ a)
    (hab : a ≤ b) (hPNT : ∀ t : Real, 2 ≤ t ->
      |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |(∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
        realWeight X p) - Real.log (b / a) / Real.log X| ≤
      (C / (Real.log X * Real.log b) + Real.log b / (b * Real.log X)) +
        (C / (Real.log X * Real.log a) + Real.log a / (a * Real.log X)) +
        C / Real.log X * Real.log (Real.log b / Real.log a) := by
  have ha1 : 1 < a := by
    linarith [Real.exp_one_gt_d9]
  have ha2 : 2 ≤ a := by
    linarith [Real.exp_one_gt_d9]
  have hb1 : 1 < b := ha1.trans_le hab
  have hb2 : 2 ≤ b := ha2.trans hab
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hf_cont : ContinuousOn (realWeight X) (Set.Icc a b) := by
    unfold realWeight
    have hlog : ContinuousOn Real.log (Set.Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
    exact hlog.div (continuousOn_id.mul continuousOn_const) (by
        intro t ht
        exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1)))
          (ne_of_gt hlogX))
  have hf_diff : ∀ t ∈ Set.Ioo a b,
      DifferentiableAt Real (realWeight X) t := by
    intro t ht
    exact (realWeight_hasDerivAt
      (ne_of_gt (zero_lt_one.trans (ha1.trans ht.1)))
      (ne_of_gt hlogX)).differentiableAt
  have hexpr : IntervalIntegrable
      (fun t : Real => (1 - Real.log t) /
        (t ^ 2 * Real.log X)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hlog : ContinuousOn Real.log (Set.Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
    apply (continuousOn_const.sub hlog).div
      ((continuousOn_id.pow 2).mul continuousOn_const)
    intro t ht
    exact mul_ne_zero
      (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))))
      (ne_of_gt hlogX)
  have hf_int : IntervalIntegrable (deriv (realWeight X)) volume a b := by
    exact hexpr.congr (by
      intro t ht
      symm
      exact realWeight_deriv
        (ne_of_gt (zero_lt_one.trans (ha1.trans_le (by
          rw [uIoc_of_le hab] at ht
          exact ht.1.le)))) (ne_of_gt hlogX))
  have hdecomp := sum_prime_halfOpen_eq_main_add_remainders
    ha1 hab hf_cont hf_diff hf_int
  have hzero : 0 ∉ uIcc a b := by
    rw [uIcc_of_le hab]; intro h
    exact (not_le.mpr (zero_lt_one.trans ha1)) h.1
  have hmain : (∫ t in a..b,
      realWeight X t / Real.log t) =
      Real.log (b / a) / Real.log X := by
    rw [show (∫ t in a..b, realWeight X t / Real.log t) =
        ∫ t in a..b, (1 / Real.log X) * (1 / t) by
      apply intervalIntegral.integral_congr
      intro t ht
      have hta : a ≤ t := by
        rw [uIcc_of_le hab] at ht
        exact ht.1
      have ht1 : 1 < t := ha1.trans_le hta
      have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1)
      have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
      unfold realWeight
      field_simp [ht0, hlt, ne_of_gt hlogX]
      , intervalIntegral.integral_const_mul]
    simpa only [one_div, inv_mul_eq_div] using
      congrArg (fun y : Real => y / Real.log X) (integral_one_div hzero)
  have hBa := realWeight_boundary_le hC hX ha2 (hPNT a ha2)
  have hBb := realWeight_boundary_le hC hX hb2 (hPNT b hb2)
  have hInt := realWeight_remainderIntegral_le hC hX ha hab hPNT
  rw [hdecomp, hmain]
  have hcancel :
      Real.log (b / a) / Real.log X +
          realWeight X b * strictPrimeRemainder b -
          realWeight X a * strictPrimeRemainder a -
          (∫ t in a..b, deriv (realWeight X) t * primeRemainder t) -
        Real.log (b / a) / Real.log X =
      (realWeight X b * strictPrimeRemainder b -
        realWeight X a * strictPrimeRemainder a) -
        (∫ t in a..b, deriv (realWeight X) t * primeRemainder t) := by
    ring
  rw [hcancel]
  calc
    |(realWeight X b * strictPrimeRemainder b -
          realWeight X a * strictPrimeRemainder a) -
        (∫ t in a..b, deriv (realWeight X) t * primeRemainder t)| ≤
        |realWeight X b * strictPrimeRemainder b| +
          |realWeight X a * strictPrimeRemainder a| +
          |(∫ t in a..b, deriv (realWeight X) t * primeRemainder t)| := by
      exact (abs_sub _ _).trans (add_le_add
        (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hBb hBa) hInt

private theorem abs_sum_sub_sum_le_two_mul_of_endpoint_cards {s t : Finset Nat}
    {f : Nat → Real} {M : Real}
    (hM : 0 ≤ M) (hf0 : ∀ n ∈ s ∪ t, 0 ≤ f n)
    (hfM : ∀ n ∈ (s \ t) ∪ (t \ s), f n ≤ M)
    (hst : #(s \ t) ≤ 1) (hts : #(t \ s) ≤ 1) :
    |(∑ n ∈ s, f n) - ∑ n ∈ t, f n| ≤ 2 * M := by
  classical
  have hsDecomp : (∑ n ∈ s, f n) =
      (∑ n ∈ s \ t, f n) + ∑ n ∈ s ∩ t, f n := by
    have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : s ∩ t ⊆ s)
    rw [show s \ (s ∩ t) = s \ t by ext n; simp] at h
    linarith
  have htDecomp : (∑ n ∈ t, f n) =
      (∑ n ∈ t \ s, f n) + ∑ n ∈ s ∩ t, f n := by
    have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : s ∩ t ⊆ t)
    rw [show t \ (s ∩ t) = t \ s by ext n; simp] at h
    linarith
  have hdiff : (∑ n ∈ s, f n) - ∑ n ∈ t, f n =
      (∑ n ∈ s \ t, f n) - ∑ n ∈ t \ s, f n := by
    rw [hsDecomp, htDecomp]; ring
  rw [hdiff]
  have hnonnegST : 0 ≤ ∑ n ∈ s \ t, f n := Finset.sum_nonneg fun n hn =>
    hf0 n (Finset.mem_union_left t (Finset.mem_sdiff.mp hn).1)
  have hnonnegTS : 0 ≤ ∑ n ∈ t \ s, f n := Finset.sum_nonneg fun n hn =>
    hf0 n (Finset.mem_union_right s (Finset.mem_sdiff.mp hn).1)
  have hsumST : (∑ n ∈ s \ t, f n) ≤ M := by
    calc
      (∑ n ∈ s \ t, f n) ≤ #(s \ t) • M := Finset.sum_le_card_nsmul
        _ _ _ (fun n hn => hfM n (Finset.mem_union_left _ hn))
      _ ≤ 1 • M := nsmul_le_nsmul_left hM hst
      _ = M := one_nsmul _
  have hsumTS : (∑ n ∈ t \ s, f n) ≤ M := by
    calc
      (∑ n ∈ t \ s, f n) ≤ #(t \ s) • M := Finset.sum_le_card_nsmul
        _ _ _ (fun n hn => hfM n (Finset.mem_union_right _ hn))
      _ ≤ 1 • M := nsmul_le_nsmul_left hM hts
      _ = M := one_nsmul _
  calc
    |(∑ n ∈ s \ t, f n) - ∑ n ∈ t \ s, f n| ≤
        (∑ n ∈ s \ t, f n) + ∑ n ∈ t \ s, f n := by
      exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    _ ≤ M + M := add_le_add hsumST hsumTS
    _ = 2 * M := by ring

private theorem sievePrimeInterval_halfOpen_endpoint_cards
    {w z : Real} :
    #((sievePrimeInterval w z) \
      ((naturalLeftClosedRightOpenInterval w z).filter Nat.Prime)) ≤ 1 ∧
      #(((naturalLeftClosedRightOpenInterval w z).filter Nat.Prime) \
        sievePrimeInterval w z) ≤ 1 := by
  classical
  constructor <;> rw [Finset.card_le_one_iff]
  · intro p q hp hq
    simp only [Finset.mem_sdiff, mem_sievePrimeInterval, Finset.mem_filter,
      mem_naturalLeftClosedRightOpenInterval] at hp hq
    have hpz : (p : Real) = z := by
      apply le_antisymm hp.1.2.2; by_contra h
      exact hp.2 ⟨⟨hp.1.2.1.le, lt_of_not_ge h⟩, hp.1.1⟩
    have hqz : (q : Real) = z := by
      apply le_antisymm hq.1.2.2; by_contra h
      exact hq.2 ⟨⟨hq.1.2.1.le, lt_of_not_ge h⟩, hq.1.1⟩
    exact_mod_cast hpz.trans hqz.symm
  · intro p q hp hq
    simp only [Finset.mem_sdiff, Finset.mem_filter,
      mem_naturalLeftClosedRightOpenInterval, mem_sievePrimeInterval] at hp hq
    have hpw : (p : Real) = w := by
      apply le_antisymm; by_contra h
      exact hp.2 ⟨hp.1.2, lt_of_not_ge h, hp.1.1.2.le⟩
      exact hp.1.1.1
    have hqw : (q : Real) = w := by
      apply le_antisymm; by_contra h
      exact hq.2 ⟨hq.1.2, lt_of_not_ge h, hq.1.1.2.le⟩
      exact hq.1.1.1
    exact_mod_cast hpw.trans hqw.symm

private theorem realWeight_sieve_sub_halfOpen_le
    {X w z : Real} (hX : 1 < X) (hw : 2 ≤ w) (hwz : w ≤ z) :
    |(∑ p ∈ sievePrimeInterval w z, realWeight X p) -
        ∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
          realWeight X p| ≤
      2 * (Real.log z / (w * Real.log X)) := by
  classical
  let s := sievePrimeInterval w z
  let t := (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime
  let M := Real.log z / (w * Real.log X)
  have hw0 : 0 < w := by linarith
  have hz0 : 0 < z := hw0.trans_le hwz
  have hz1 : 1 ≤ z := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (Real.log_nonneg hz1)
      (mul_nonneg hw0.le hlogX.le)
  have hbounds {p : Nat} (hp : p ∈ s ∪ t) :
      w ≤ (p : Real) ∧ (p : Real) ≤ z := by
    rcases Finset.mem_union.mp hp with hpS | hpT
    · have h := mem_sievePrimeInterval.mp hpS
      exact ⟨h.2.1.le, h.2.2⟩
    · have h := Finset.mem_filter.mp hpT
      have hi := mem_naturalLeftClosedRightOpenInterval.mp h.1
      exact ⟨hi.1, hi.2.le⟩
  have hprime {p : Nat} (hp : p ∈ s ∪ t) : p.Prime := by
    rcases Finset.mem_union.mp hp with hpS | hpT
    · exact (mem_sievePrimeInterval.mp hpS).1
    · exact (Finset.mem_filter.mp hpT).2
  have hweightNonneg : ∀ p ∈ s ∪ t, 0 ≤ realWeight X p := by
    intro p hp
    have hp0 : (0 : Real) < p := by exact_mod_cast (hprime hp).pos
    unfold realWeight
    exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast (hprime hp).one_le))
      (mul_nonneg hp0.le hlogX.le)
  have hweightLe : ∀ p ∈ (s \ t) ∪ (t \ s),
      realWeight X p ≤ M := by
    intro p hp
    have hpUnion : p ∈ s ∪ t := by
      rcases Finset.mem_union.mp hp with hpST | hpTS
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hpST).1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hpTS).1
    have hpBounds := hbounds hpUnion
    have hp0 : (0 : Real) < p := hw0.trans_le hpBounds.1
    have hlogp : 0 ≤ Real.log (p : Real) :=
      Real.log_nonneg (by linarith [hpBounds.1])
    have hlogpz : Real.log (p : Real) ≤ Real.log z :=
      Real.log_le_log hp0 hpBounds.2
    dsimp [M]
    unfold realWeight
    calc
      Real.log (p : Real) / ((p : Real) * Real.log X) ≤
          Real.log z / ((p : Real) * Real.log X) := by
        exact div_le_div_of_nonneg_right hlogpz
          (mul_nonneg hp0.le hlogX.le)
      _ ≤ Real.log z / (w * Real.log X) := by
        exact div_le_div_of_nonneg_left (Real.log_nonneg hz1)
          (mul_pos hw0 hlogX) (mul_le_mul_of_nonneg_right hpBounds.1 hlogX.le)
  have hcards := sievePrimeInterval_halfOpen_endpoint_cards (w := w) (z := z)
  simpa [s, t, M] using
    abs_sum_sub_sum_le_two_mul_of_endpoint_cards hM hweightNonneg hweightLe
      hcards.1 hcards.2

theorem sieve_error_le
    {C X a b : Real} (hC : 0 < C) (hX : 1 < X) (ha : Real.exp 1 ≤ a)
    (hab : a ≤ b) (hPNT : ∀ t : Real, 2 ≤ t ->
      |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |(∑ p ∈ sievePrimeInterval a b, realWeight X p) -
        Real.log (b / a) / Real.log X| ≤
      2 * (Real.log b / (a * Real.log X)) +
        ((C / (Real.log X * Real.log b) + Real.log b / (b * Real.log X)) +
          (C / (Real.log X * Real.log a) + Real.log a / (a * Real.log X)) +
          C / Real.log X * Real.log (Real.log b / Real.log a)) := by
  have ha2 : 2 ≤ a := by
    linarith [Real.exp_one_gt_d9]
  have hsieve := realWeight_sieve_sub_halfOpen_le hX ha2 hab
  have hhalf := realWeight_halfOpen_error_le hC hX ha hab hPNT
  calc
    |(∑ p ∈ sievePrimeInterval a b, realWeight X p) -
        Real.log (b / a) / Real.log X| ≤
      |(∑ p ∈ sievePrimeInterval a b, realWeight X p) -
          ∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
            realWeight X p| +
        |(∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
            realWeight X p) - Real.log (b / a) / Real.log X| := by
      exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsieve hhalf

end NormalizedPrimeLogWeight

end

end PrimesRestrictedDigits
