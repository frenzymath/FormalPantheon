import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Abel summation for strict prime cutoffs

This file proves the half-open Abel identity used in Eq. (7.45) of
`MONTGOMERY-VAUGHAN-MNT-I`. Its derivative hypothesis is open at both
endpoints, so it permits a Buchstab seam at a power endpoint.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The number of primes strictly below a real cutoff. -/
noncomputable def realPrimeCountingLt (t : Real) : Real :=
  Nat.primeCounting' (Nat.ceil t)

theorem realPrimeCountingLt_eq_card (t : Real) :
    realPrimeCountingLt t =
      (((naturalLeftClosedRightOpenInterval 0 t).filter Nat.Prime).card : Real) := by
  unfold realPrimeCountingLt naturalLeftClosedRightOpenInterval
  rw [Nat.ceil_zero]
  simp [Nat.primeCounting', Nat.count_eq_card_filter_range]

private lemma integral_deriv_mul_strictPrefix_eq
    (c : Nat → Real) {f : Real → Real} {r s : Real} (q : Nat) (hrs : r ≤ s)
    (hf_cont : ContinuousOn f (Set.Icc r s))
    (hf_diff : ∀ t ∈ Set.Ioo r s, DifferentiableAt Real f t)
    (hf_int : IntervalIntegrable (deriv f) volume r s)
    (hceil : ∀ t ∈ Set.Ioc r s,
      t ∉ Set.range (fun n : Nat => (n : Real)) → Nat.ceil t = q) :
    (∫ t in r..s, deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k) =
      (f s - f r) * ∑ k ∈ Finset.range q, c k := by
  have hnull : volume (Set.range (fun n : Nat => (n : Real))) = 0 :=
    Set.countable_range (fun n : Nat => (n : Real)) |>.measure_zero volume
  calc
    (∫ t in r..s, deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k) =
        ∫ t in r..s, deriv f t * ∑ k ∈ Finset.range q, c k := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
      intro htrs
      rw [hceil t (by simpa [Set.uIoc_of_le hrs] using htrs) ht]
    _ = (f s - f r) * ∑ k ∈ Finset.range q, c k := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_deriv_eq_sub_uIoo]
      · simpa [Set.uIcc_of_le hrs] using hf_cont
      · simpa [Set.uIoo_of_le hrs] using hf_diff
      · exact hf_int

private lemma intervalIntegrable_deriv_mul_strictPrefix
    (c : Nat → Real) {f : Real → Real} {r s : Real} (q : Nat) (hrs : r ≤ s)
    (hf_int : IntervalIntegrable (deriv f) volume r s)
    (hceil : ∀ t ∈ Set.Ioc r s,
      t ∉ Set.range (fun n : Nat => (n : Real)) → Nat.ceil t = q) :
    IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k)
      volume r s := by
  have hnull : volume (Set.range (fun n : Nat => (n : Real))) = 0 :=
    Set.countable_range (fun n : Nat => (n : Real)) |>.measure_zero volume
  apply (hf_int.mul_const (∑ k ∈ Finset.range q, c k)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)] with t htrs ht
  rw [hceil t (by simpa [Set.uIoc_of_le hrs] using htrs) ht]

/-- Abel summation over the exact natural carrier `[a,b)`. -/
theorem sum_mul_eq_sub_sub_integral_mul_strict
    (c : Nat → Real) {f : Real → Real} {a b : Real}
    (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt Real f t)
    (hf_int : IntervalIntegrable (deriv f) volume a b) :
    (∑ k ∈ naturalLeftClosedRightOpenInterval a b, f k * c k) =
      f b * (∑ k ∈ Finset.range (Nat.ceil b), c k) -
      f a * (∑ k ∈ Finset.range (Nat.ceil a), c k) -
      ∫ t in a..b,
        deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k := by
  let m := Nat.ceil a
  let n := Nat.ceil b
  have hmn : m ≤ n := Nat.ceil_mono hab
  have hma : m = Nat.ceil a := rfl
  have hnb : n = Nat.ceil b := rfl
  let g : Real → Real := fun t =>
    deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k
  have hcont_local {r s : Real} (har : a ≤ r) (hsb : s ≤ b) :
      ContinuousOn f (Set.Icc r s) :=
    hf_cont.mono (Set.Icc_subset_Icc har hsb)
  have hdiff_local {r s : Real} (har : a ≤ r) (hsb : s ≤ b) :
      ∀ t ∈ Set.Ioo r s, DifferentiableAt Real f t := by
    intro t ht
    exact hf_diff t ((Set.Ioo_subset_Ioo har hsb) ht)
  have hint_local {r s : Real} (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b) :
      IntervalIntegrable (deriv f) volume r s :=
    hf_int.mono_set (by
      simpa [Set.uIcc_of_le hab, Set.uIcc_of_le hrs] using
        (Set.Icc_subset_Icc har hsb))
  by_cases heq : m = n
  · have hceil : ∀ t ∈ Set.Ioc a b,
        t ∉ Set.range (fun k : Nat => (k : Real)) → Nat.ceil t = m := by
      intro t ht _
      apply le_antisymm
      · calc
          Nat.ceil t ≤ Nat.ceil b := Nat.ceil_mono ht.2
          _ = n := hnb.symm
          _ = m := heq.symm
      · calc
          m = Nat.ceil a := hma
          _ ≤ Nat.ceil t := Nat.ceil_mono ht.1.le
    have hI := integral_deriv_mul_strictPrefix_eq c m hab hf_cont hf_diff hf_int hceil
    rw [naturalLeftClosedRightOpenInterval,
      show Nat.ceil a = m from hma.symm,
      show Nat.ceil b = m by rw [← hnb, ← heq]]
    simp only [Finset.Ico_self, Finset.sum_empty]
    rw [hI]
    ring
  · have hlt : m < n := lt_of_le_of_ne hmn heq
    have hn_pos : 0 < n := by omega
    have ha_m : a ≤ (m : Real) := by simpa [m] using Nat.le_ceil a
    have hm_b : (m : Real) ≤ b :=
      (Nat.lt_ceil.mp (by simpa [n] using hlt)).le
    have hm_nm1_nat : m ≤ n - 1 := Nat.le_sub_one_of_lt hlt
    have hm_nm1 : (m : Real) ≤ (n - 1 : Nat) := by exact_mod_cast hm_nm1_nat
    have hnm1_b : ((n - 1 : Nat) : Real) ≤ b := by
      apply le_of_lt
      apply Nat.lt_ceil.mp
      simpa [n] using (Nat.sub_lt (by omega : 0 < n) (by omega : 0 < 1))
    have hceil_left : ∀ t ∈ Set.Ioc a (m : Real),
        t ∉ Set.range (fun k : Nat => (k : Real)) → Nat.ceil t = m := by
      intro t ht _
      apply le_antisymm
      · simpa using Nat.ceil_mono ht.2
      · rw [hma]
        exact Nat.ceil_mono ht.1.le
    have hceil_unit (i : Nat) : ∀ t ∈ Set.Ioc (i : Real) (i + 1 : Nat),
        t ∉ Set.range (fun k : Nat => (k : Real)) → Nat.ceil t = i + 1 := by
      intro t ht _
      exact (Nat.ceil_eq_iff (Nat.succ_ne_zero i)).mpr (by simpa using ht)
    have hceil_right : ∀ t ∈ Set.Ioc ((n - 1 : Nat) : Real) b,
        t ∉ Set.range (fun k : Nat => (k : Real)) → Nat.ceil t = n := by
      intro t ht _
      apply le_antisymm
      · rw [hnb]
        exact Nat.ceil_mono ht.2
      · have h : n - 1 + 1 ≤ Nat.ceil t :=
          Nat.add_one_le_ceil_iff.mpr ht.1
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
    have hleft := integral_deriv_mul_strictPrefix_eq c m ha_m
      (hcont_local le_rfl hm_b) (hdiff_local le_rfl hm_b)
      (hint_local le_rfl ha_m hm_b) hceil_left
    have hright := integral_deriv_mul_strictPrefix_eq c n hnm1_b
      (hcont_local (ha_m.trans hm_nm1) le_rfl)
      (hdiff_local (ha_m.trans hm_nm1) le_rfl)
      (hint_local (ha_m.trans hm_nm1) hnm1_b le_rfl) hceil_right
    have hunit (i : Nat) (hi : i ∈ Finset.Ico m (n - 1)) :
        (∫ t in (i : Real)..(i + 1 : Nat), g t) =
          (f (i + 1) - f i) * ∑ k ∈ Finset.range (i + 1), c k := by
      have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
      have hin : i + 1 ≤ n - 1 := (Finset.mem_Ico.mp hi).2
      have hai : a ≤ (i : Real) := ha_m.trans (by exact_mod_cast hmi)
      have hib : ((i + 1 : Nat) : Real) ≤ b :=
        (by exact_mod_cast hin : ((i + 1 : Nat) : Real) ≤ (n - 1 : Nat)).trans hnm1_b
      simpa [g] using integral_deriv_mul_strictPrefix_eq c (i + 1)
        (by exact_mod_cast i.le_succ : (i : Real) ≤ (i + 1 : Nat))
        (hcont_local hai hib) (hdiff_local hai hib)
        (hint_local hai (by exact_mod_cast i.le_succ) hib) (hceil_unit i)
    have hint_left : IntervalIntegrable g volume a (m : Real) := by
      simpa [g] using intervalIntegrable_deriv_mul_strictPrefix c m ha_m
        (hint_local le_rfl ha_m hm_b) hceil_left
    have hint_unit (i : Nat) (hi : i ∈ Finset.Ico m (n - 1)) :
        IntervalIntegrable g volume (i : Real) (i + 1 : Nat) := by
      have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
      have hin : i + 1 ≤ n - 1 := (Finset.mem_Ico.mp hi).2
      have hai : a ≤ (i : Real) := ha_m.trans (by exact_mod_cast hmi)
      have hib : ((i + 1 : Nat) : Real) ≤ b :=
        (by exact_mod_cast hin : ((i + 1 : Nat) : Real) ≤ (n - 1 : Nat)).trans hnm1_b
      simpa [g] using intervalIntegrable_deriv_mul_strictPrefix c (i + 1)
        (by exact_mod_cast i.le_succ : (i : Real) ≤ (i + 1 : Nat))
        (hint_local hai (by exact_mod_cast i.le_succ) hib) (hceil_unit i)
    have hint_mid : IntervalIntegrable g volume (m : Real) (n - 1 : Nat) :=
      IntervalIntegrable.trans_iterate_Ico hm_nm1_nat (fun i hi =>
        hint_unit i (by simpa [Finset.mem_Ico] using hi))
    have hint_right : IntervalIntegrable g volume ((n - 1 : Nat) : Real) b := by
      simpa [g] using intervalIntegrable_deriv_mul_strictPrefix c n hnm1_b
        (hint_local (ha_m.trans hm_nm1) hnm1_b le_rfl) hceil_right
    have hmid : (∫ t in (m : Real)..(n - 1 : Nat), g t) =
        ∑ i ∈ Finset.Ico m (n - 1),
          (f (i + 1) - f i) * ∑ k ∈ Finset.range (i + 1), c k := by
      rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico hm_nm1_nat (fun i hi =>
        hint_unit i (by simpa [Finset.mem_Ico] using hi))]
      exact Finset.sum_congr rfl hunit
    have hsplit : (∫ t in a..b, g t) =
        (∫ t in a..(m : Real), g t) +
        (∫ t in (m : Real)..(n - 1 : Nat), g t) +
        ∫ t in ((n - 1 : Nat) : Real)..b, g t := by
      rw [intervalIntegral.integral_add_adjacent_intervals hint_left hint_mid,
        intervalIntegral.integral_add_adjacent_intervals (hint_left.trans hint_mid) hint_right]
    have hparts := Finset.sum_Ico_by_parts (fun k : Nat => f k) c hlt
    change (∑ k ∈ Finset.Ico m n, f k * c k) = _
    rw [show (∑ k ∈ Finset.Ico m n, f k * c k) =
        f ((n - 1 : Nat) : Real) * (∑ k ∈ Finset.range n, c k) -
        f m * (∑ k ∈ Finset.range m, c k) -
        ∑ i ∈ Finset.Ico m (n - 1),
          (f ((i + 1 : Nat) : Real) - f i) *
            ∑ k ∈ Finset.range (i + 1), c k by
      simpa [smul_eq_mul] using hparts]
    rw [show (∫ t in a..b,
        deriv f t * ∑ k ∈ Finset.range (Nat.ceil t), c k) =
        (f m - f a) * (∑ k ∈ Finset.range m, c k) +
        (∑ i ∈ Finset.Ico m (n - 1),
          (f ((i + 1 : Nat) : Real) - f i) *
            ∑ k ∈ Finset.range (i + 1), c k) +
        (f b - f ((n - 1 : Nat) : Real)) *
          (∑ k ∈ Finset.range n, c k) by
      simpa [g, hleft, hmid, hright] using hsplit]
    ring

/-- Abel summation specialized to primes strictly below the upper real endpoint. -/
theorem sum_prime_halfOpen_eq_boundary_sub_integral
    {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt Real f t)
    (hf_int : IntervalIntegrable (deriv f) volume a b) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime, f p) =
      f b * realPrimeCountingLt b -
      f a * realPrimeCountingLt a -
      ∫ t in a..b, deriv f t * realPrimeCountingLt t := by
  let c : Nat → Real := fun n => if Nat.Prime n then 1 else 0
  have h := sum_mul_eq_sub_sub_integral_mul_strict c hab hf_cont hf_diff hf_int
  have hprefix (r : Real) :
      (∑ k ∈ Finset.range (Nat.ceil r), c k) = realPrimeCountingLt r := by
    simp [c, realPrimeCountingLt, Nat.primeCounting', Nat.count_eq_card_filter_range]
  simp_rw [hprefix] at h
  rw [← h]
  simp only [c, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  simp

end PrimesRestrictedDigits
