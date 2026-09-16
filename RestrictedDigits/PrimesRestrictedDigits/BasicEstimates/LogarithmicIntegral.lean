import PrimesRestrictedDigits.BasicEstimates.PrimeCountingBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The logarithmic integral and prime-counting remainders

This file defines the normalization used in `MONTGOMERY-VAUGHAN-MNT-I`,
Theorem 6.9, and derives the exact strict-endpoint decomposition in Eq. (7.45).
-/

open Finset MeasureTheory Set
open scoped BigOperators Topology

namespace PrimesRestrictedDigits

/-- The logarithmic integral normalized to vanish at two. -/
noncomputable def logarithmicIntegral (x : Real) : Real :=
  ∫ u in (2 : Real)..x, 1 / Real.log u

private lemma continuousOn_one_div_log {a b : Real} (ha : 1 < a) (hb : 1 < b) :
    ContinuousOn (fun u : Real => 1 / Real.log u) (Set.uIcc a b) := by
  have hlog : ContinuousOn Real.log (Set.uIcc a b) := by
    apply Real.continuousOn_log.mono
    intro u hu
    rw [Set.mem_compl_singleton_iff]
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hu
      exact ne_of_gt ((zero_lt_one.trans ha).trans_le hu.1)
    · rw [Set.uIcc_of_ge hba] at hu
      exact ne_of_gt ((zero_lt_one.trans hb).trans_le hu.1)
  simpa only [one_div, Pi.inv_def] using hlog.inv₀ (fun u hu => by
    have hu1 : 1 < u := by
      rcases le_total a b with hab | hba
      · rw [Set.uIcc_of_le hab] at hu
        exact lt_of_lt_of_le ha hu.1
      · rw [Set.uIcc_of_ge hba] at hu
        exact lt_of_lt_of_le hb hu.1
    exact ne_of_gt (Real.log_pos hu1))

private lemma continuousAt_one_div_log {x : Real} (hx : 1 < x) :
    ContinuousAt (fun u : Real => 1 / Real.log u) x := by
  simpa only [one_div, Pi.inv_def] using
    (Real.continuousAt_log (ne_of_gt (lt_trans zero_lt_one hx))).inv₀
      (ne_of_gt (Real.log_pos hx))

theorem logarithmicIntegral_hasDerivAt {x : Real} (hx : 1 < x) :
    HasDerivAt logarithmicIntegral (1 / Real.log x) x := by
  have hcont : ContinuousOn (fun u : Real => 1 / Real.log u) (Set.uIcc 2 x) := by
    apply continuousOn_one_div_log (by norm_num) hx
  have hint : IntervalIntegrable (fun u : Real => 1 / Real.log u) volume 2 x :=
    hcont.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter
      (fun u : Real => 1 / Real.log u) (𝓝 x) volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun u hu => continuousAt_one_div_log hu) x hx
  change HasDerivAt (fun u : Real => ∫ z in (2 : Real)..u, 1 / Real.log z)
    (1 / Real.log x) x
  simpa using intervalIntegral.integral_hasDerivAt_right hint hmeas
    (continuousAt_one_div_log hx)

theorem logarithmicIntegral_deriv {x : Real} (hx : 1 < x) :
    deriv logarithmicIntegral x = 1 / Real.log x :=
  (logarithmicIntegral_hasDerivAt hx).deriv

theorem logarithmicIntegral_continuousOn :
    ContinuousOn logarithmicIntegral (Set.Ioi 1) := by
  intro x hx
  exact (logarithmicIntegral_hasDerivAt hx).continuousAt.continuousWithinAt

private lemma intervalIntegrable_deriv_mul_realPrimeCounting
    {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hf : IntervalIntegrable (deriv f) volume a b) :
    IntervalIntegrable (fun t => deriv f t * realPrimeCounting t) volume a b := by
  have hf_on : IntegrableOn (deriv f) (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hf
  have hm : AEStronglyMeasurable realPrimeCounting
      (volume.restrict (Set.Icc a b)) :=
    measurable_realPrimeCounting.aestronglyMeasurable
  let C : Real := realPrimeCounting b
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      ‖realPrimeCounting t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hfloor : Nat.floor t ≤ Nat.floor b := Nat.floor_mono ht.2
    have hcount : Nat.primeCounting (Nat.floor t) ≤
        Nat.primeCounting (Nat.floor b) := Nat.monotone_primeCounting hfloor
    rw [show realPrimeCounting t =
      (Nat.primeCounting (Nat.floor t) : Real) by rfl,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (Nat.primeCounting (Nat.floor t) : Real) ≤
      (Nat.primeCounting (Nat.floor b) : Real)
    exact_mod_cast hcount
  have htop : MemLp realPrimeCounting ⊤
      (volume.restrict (Set.Icc a b)) :=
    memLp_top_of_bound hm C hbound
  have hprod : Integrable
      (fun t => realPrimeCounting t * deriv f t)
      (volume.restrict (Set.Icc a b)) :=
    hf_on.mul_of_top_right htop
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  simpa [IntegrableOn, mul_comm] using hprod

/-- The left-limit prime-counting remainder used at strict boundaries. -/
noncomputable def strictPrimeRemainder (t : Real) : Real :=
  realPrimeCountingLt t - logarithmicIntegral t

/-- The conventional weak prime-counting remainder used in the interior. -/
noncomputable def primeRemainder (t : Real) : Real :=
  realPrimeCounting t - logarithmicIntegral t

theorem abs_strictPrimeRemainder_sub_primeRemainder_le_one (t : Real) :
    |strictPrimeRemainder t - primeRemainder t| ≤ 1 := by
  unfold strictPrimeRemainder primeRemainder
  rw [show (realPrimeCountingLt t - logarithmicIntegral t) -
      (realPrimeCounting t - logarithmicIntegral t) =
      realPrimeCountingLt t - realPrimeCounting t by ring]
  exact abs_realPrimeCountingLt_sub_realPrimeCounting_le_one t

/-- Eq. (7.45) with strict endpoint and weak interior PNT remainders. -/
theorem sum_prime_halfOpen_eq_main_add_remainders
    {f : Real → Real} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt Real f t)
    (hf_int : IntervalIntegrable (deriv f) volume a b) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime, f p) =
      (∫ t in a..b, f t / Real.log t) +
      f b * strictPrimeRemainder b - f a * strictPrimeRemainder a -
      ∫ t in a..b, deriv f t * primeRemainder t := by
  have hli_cont : ContinuousOn logarithmicIntegral (Set.Icc a b) :=
    logarithmicIntegral_continuousOn.mono (by
      intro t ht
      exact lt_of_lt_of_le ha ht.1)
  have hli_mul_int : IntervalIntegrable
      (fun t => deriv f t * logarithmicIntegral t) volume a b :=
    hf_int.mul_continuousOn (by simpa [Set.uIcc_of_le hab] using hli_cont)
  have hprime_int : IntervalIntegrable
      (fun t => deriv f t * realPrimeCounting t) volume a b :=
    intervalIntegrable_deriv_mul_realPrimeCounting hab hf_int
  have hli_int : IntervalIntegrable (fun t : Real => 1 / Real.log t) volume a b :=
    (continuousOn_one_div_log ha (lt_of_lt_of_le ha hab)).intervalIntegrable
  have habel := sum_prime_halfOpen_eq_boundary_sub_integral
    (f := f) hab hf_cont hf_diff hf_int
  have hmain :
      f b * logarithmicIntegral b - f a * logarithmicIntegral a -
          ∫ t in a..b, deriv f t * logarithmicIntegral t =
        ∫ t in a..b, f t / Real.log t := by
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := f) (u' := deriv f)
      (v := logarithmicIntegral) (v' := fun t => 1 / Real.log t)
      (hf_cont.mono (Set.uIcc_of_le hab ▸ Set.Icc_subset_Icc le_rfl le_rfl))
      (hli_cont.mono (Set.uIcc_of_le hab ▸ Set.Icc_subset_Icc le_rfl le_rfl))
      (fun t ht => (hf_diff t (by
        simpa [min_eq_left hab, max_eq_right hab] using ht)).hasDerivAt)
      (fun t ht => logarithmicIntegral_hasDerivAt (by
        have ht' : t ∈ Set.Ioo a b := by
          simpa [min_eq_left hab, max_eq_right hab] using ht
        exact lt_trans ha ht'.1))
      hf_int hli_int
    simpa [one_div, div_eq_mul_inv, mul_comm] using hparts.symm
  rw [habel]
  have hcounts :
      (∫ t in a..b, deriv f t * realPrimeCountingLt t) =
        ∫ t in a..b, deriv f t * realPrimeCounting t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [realPrimeCountingLt_ae_eq_realPrimeCounting] with t ht
    intro hmem
    rw [ht]
  rw [show strictPrimeRemainder b =
      realPrimeCountingLt b - logarithmicIntegral b by rfl,
    show strictPrimeRemainder a =
      realPrimeCountingLt a - logarithmicIntegral a by rfl,
    hcounts]
  change _ = _ - ∫ t in a..b,
    deriv f t * (realPrimeCounting t - logarithmicIntegral t)
  have hsplit := intervalIntegral.integral_sub hprime_int hli_mul_int
  have hsplit' :
      (∫ t in a..b, deriv f t *
        (realPrimeCounting t - logarithmicIntegral t)) =
        (∫ t in a..b, deriv f t * realPrimeCounting t) -
          ∫ t in a..b, deriv f t * logarithmicIntegral t := by
    simpa only [mul_sub] using hsplit
  rw [hsplit', ← hmain]
  ring

end PrimesRestrictedDigits
