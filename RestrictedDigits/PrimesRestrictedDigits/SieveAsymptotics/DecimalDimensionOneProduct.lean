import PrimesRestrictedDigits.PrimeNumberTheorem.ReciprocalPrimeMertens
import Mathlib.Analysis.Complex.Exponential

/-!
# The decimal dimension-one sieve product

This proves the `kappa=1` specialization of `IWANIEC-ROSSER-SIEVE-1980`, Eq. (1.3), p. 171,
for primes not dividing ten.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The inverse Euler product on the exact half-open interval `[w,z)`, with
the decimal primes two and five omitted. -/
def decimalIntervalPrimeInverseProduct (w z : Real) : Real :=
  ∏ p ∈ (naturalLeftClosedRightOpenInterval w z).filter
      (fun p ↦ p.Prime ∧ ¬p ∣ 10),
    (1 - (p : Real)⁻¹)⁻¹

private theorem reciprocal_mul_sub_one_eq_sub {k : Nat} (hk : 2 ≤ k) :
    1 / ((k : Real) * ((k : Real) - 1)) =
      1 / ((k : Real) - 1) - 1 / (k : Real) := by
  have hk0 : (k : Real) ≠ 0 := by positivity
  have hksub0 : (k : Real) - 1 ≠ 0 := by
    have hkReal : (2 : Real) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  ring

private theorem sum_Ico_reciprocal_mul_sub_one_eq
    {m n : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (∑ k ∈ Finset.Ico m n,
      1 / ((k : Real) * ((k : Real) - 1))) =
      1 / ((m : Real) - 1) - 1 / ((n : Real) - 1) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top hmn, ih,
        reciprocal_mul_sub_one_eq_sub (hm.trans hmn)]
      push_cast
      ring

private theorem sum_prime_reciprocal_mul_sub_one_le
    {w z : Real} (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
      1 / ((p : Real) * ((p : Real) - 1))) ≤ 1 / (w - 1) := by
  let m := Nat.ceil w
  let n := Nat.ceil z
  have hm : 2 ≤ m := by
    exact_mod_cast hw.trans (Nat.le_ceil w)
  have hmn : m ≤ n := Nat.ceil_mono hwz
  have hn : 2 ≤ n := hm.trans hmn
  have hmCast : w ≤ (m : Real) := by simpa [m] using Nat.le_ceil w
  have hmReal : (2 : Real) ≤ m := by exact_mod_cast hm
  have hnReal : (2 : Real) ≤ n := by exact_mod_cast hn
  have hmDen : 0 < (m : Real) - 1 := by linarith
  have hnDen : 0 < (n : Real) - 1 := by linarith
  have hwDen : 0 < w - 1 := by linarith
  calc
    (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
        1 / ((p : Real) * ((p : Real) - 1))) ≤
        ∑ p ∈ naturalLeftClosedRightOpenInterval w z,
          1 / ((p : Real) * ((p : Real) - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p hpInterval hpNotPrime
        have hpBounds :=
          mem_naturalLeftClosedRightOpenInterval.mp hpInterval
        have hpTwo : (2 : Real) ≤ p := hw.trans hpBounds.1
        have hpPos : (0 : Real) < p := by linarith
        have hpSubPos : (0 : Real) < (p : Real) - 1 := by linarith
        exact div_nonneg zero_le_one (mul_nonneg hpPos.le hpSubPos.le)
    _ = 1 / ((m : Real) - 1) - 1 / ((n : Real) - 1) := by
      simpa [naturalLeftClosedRightOpenInterval, m, n] using
        sum_Ico_reciprocal_mul_sub_one_eq hm hmn
    _ ≤ 1 / ((m : Real) - 1) := by
      have : 0 ≤ 1 / ((n : Real) - 1) := by positivity
      linarith
    _ ≤ 1 / (w - 1) := by
      exact one_div_le_one_div_of_le hwDen (by linarith)

private theorem allPrimeInverseProduct_le
    {D w z : Real} (hw : 2 ≤ w) (hwz : w ≤ z)
    (hrecip :
      (∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
        (p : Real)⁻¹) ≤
        Real.log (Real.log z / Real.log w) + D / Real.log w) :
    (∏ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
      (1 - (p : Real)⁻¹)⁻¹) ≤
      (Real.log z / Real.log w) *
        Real.exp ((D + 1) / Real.log w) := by
  let S := (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime
  let g : Nat → Real := fun p ↦
    if p.Prime then 1 / ((p : Real) - 1) else 0
  have hw0 : 0 < w := by linarith
  have hw1 : 1 < w := by linarith
  have hz1 : 1 < z := hw1.trans_le hwz
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hratio : 0 < Real.log z / Real.log w := div_pos hlogz hlogw
  have hg : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    split_ifs with hp
    · have hpReal : (1 : Real) < p := by exact_mod_cast hp.one_lt
      positivity
    · positivity
  have hfactor (p : Nat) (hp : p ∈ S) :
      (1 - (p : Real)⁻¹)⁻¹ = 1 + g p := by
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hp1 : (p : Real) - 1 ≠ 0 := by
      have hpReal : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
      exact ne_of_gt (sub_pos.mpr hpReal)
    rw [show g p = 1 / ((p : Real) - 1) by simp [g, hpPrime]]
    field_simp [hp0, hp1]
    ring
  have hprodExp :
      (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) ≤
        Real.exp (∑ p ∈ S, 1 / ((p : Real) - 1)) := by
    calc
      (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) =
          ∏ p ∈ S, (1 + g p) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hfactor p hp
      _ ≤ Real.exp (∑ p ∈ S, g p) :=
        Real.prod_one_add_le_exp_sum S hg
      _ = Real.exp (∑ p ∈ S, 1 / ((p : Real) - 1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        have hpPrime := (Finset.mem_filter.mp hp).2
        simp [g, hpPrime]
  have hcorr := sum_prime_reciprocal_mul_sub_one_le hw hwz
  have hlogLe : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hcorrLog : 1 / (w - 1) ≤ 1 / Real.log w :=
    one_div_le_one_div_of_le hlogw hlogLe
  have hsumSplit :
      (∑ p ∈ S, 1 / ((p : Real) - 1)) =
        (∑ p ∈ S, (p : Real)⁻¹) +
          ∑ p ∈ S,
            1 / ((p : Real) * ((p : Real) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hp1 : (p : Real) - 1 ≠ 0 := by
      have hpReal : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
      exact ne_of_gt (sub_pos.mpr hpReal)
    field_simp [hp0, hp1]
    ring
  have hsum :
      (∑ p ∈ S, 1 / ((p : Real) - 1)) ≤
        Real.log (Real.log z / Real.log w) +
          (D + 1) / Real.log w := by
    rw [hsumSplit]
    calc
      _ ≤ (Real.log (Real.log z / Real.log w) + D / Real.log w) +
          1 / (w - 1) := add_le_add hrecip hcorr
      _ ≤ (Real.log (Real.log z / Real.log w) + D / Real.log w) +
          1 / Real.log w := by gcongr
      _ = _ := by ring
  calc
    (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) ≤
        Real.exp (∑ p ∈ S, 1 / ((p : Real) - 1)) := hprodExp
    _ ≤ Real.exp (Real.log (Real.log z / Real.log w) +
        (D + 1) / Real.log w) := Real.exp_le_exp.mpr hsum
    _ = (Real.log z / Real.log w) *
        Real.exp ((D + 1) / Real.log w) := by
      rw [Real.exp_add, Real.exp_log hratio]

private theorem exp_le_one_add_mul_self_exp (x : Real) :
    Real.exp x ≤ 1 + x * Real.exp x := by
  have hbase := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos x).le
  rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero x)] at hmul
  nlinarith

private theorem exp_div_log_le_one_add
    {E w : Real} (hE : 0 ≤ E) (hw : 2 ≤ w) :
    Real.exp (E / Real.log w) ≤
      1 + E * Real.exp (E / Real.log 2) / Real.log w := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogLe : Real.log 2 ≤ Real.log w :=
    Real.log_le_log (by norm_num) hw
  have hxNonneg : 0 ≤ E / Real.log w := div_nonneg hE hlogW.le
  have hxLe : E / Real.log w ≤ E / Real.log 2 :=
    div_le_div_of_nonneg_left hE hlogTwo hlogLe
  calc
    Real.exp (E / Real.log w) ≤
        1 + (E / Real.log w) * Real.exp (E / Real.log w) :=
      exp_le_one_add_mul_self_exp _
    _ ≤ 1 + (E / Real.log w) * Real.exp (E / Real.log 2) := by
      gcongr
    _ = 1 + E * Real.exp (E / Real.log 2) / Real.log w := by ring

/-- The decimal inverse product satisfies Iwaniec's dimension-one hypothesis
with one absolute coefficient chosen before both interval endpoints. -/
theorem exists_decimalDimensionOneProduct_bound :
    ∃ K : Real, 2 ≤ K ∧ ∀ w z : Real, 2 ≤ w → w < z →
      decimalIntervalPrimeInverseProduct w z <
        (Real.log z / Real.log w) * (1 + K / Real.log w) := by
  obtain ⟨D, hD, hrecip⟩ :=
    exists_sum_prime_inv_halfOpen_le_log_ratio
  let E : Real := D + 1
  let K : Real := 2 + E * Real.exp (E / Real.log 2)
  have hE : 0 < E := by dsimp [E]; linarith
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    have : 0 < E * Real.exp (E / Real.log 2) :=
      mul_pos hE (Real.exp_pos _)
    linarith
  intro w z hw hwz
  let I := naturalLeftClosedRightOpenInterval w z
  let S := I.filter Nat.Prime
  let T := I.filter (fun p ↦ p.Prime ∧ ¬p ∣ 10)
  have hw0 : 0 < w := by linarith
  have hw1 : 1 < w := by linarith
  have hz1 : 1 < z := hw1.trans hwz
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hratio : 0 < Real.log z / Real.log w := div_pos hlogz hlogw
  have hTS : T ⊆ S := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  have hTnonneg : ∀ p ∈ T, 0 ≤ (1 - (p : Real)⁻¹)⁻¹ := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2.1
    have hpReal : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    exact inv_nonneg.mpr
      (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpReal)).le
  have hExtra : ∀ p ∈ S, p ∉ T → 1 ≤ (1 - (p : Real)⁻¹)⁻¹ := by
    intro p hpS hpT
    have hpPrime := (Finset.mem_filter.mp hpS).2
    have hpReal : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hpos : 0 < 1 - (p : Real)⁻¹ :=
      sub_pos.mpr (inv_lt_one_of_one_lt₀ hpReal)
    apply (one_le_inv₀ hpos).mpr
    have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have : 0 < (p : Real)⁻¹ := inv_pos.mpr hp0
    linarith
  have hsubsetProduct :
      (∏ p ∈ T, (1 - (p : Real)⁻¹)⁻¹) ≤
        ∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹ :=
    Finset.prod_le_prod_of_subset_of_one_le hTS hTnonneg hExtra
  have hall := allPrimeInverseProduct_le hw hwz.le
    (hrecip w z hw hwz.le)
  have hexp := exp_div_log_le_one_add hE.le hw
  have hsmall :
      (Real.log z / Real.log w) * Real.exp (E / Real.log w) ≤
        (Real.log z / Real.log w) *
          (1 + E * Real.exp (E / Real.log 2) / Real.log w) := by
    gcongr
  have hstrict :
      (Real.log z / Real.log w) *
          (1 + E * Real.exp (E / Real.log 2) / Real.log w) <
        (Real.log z / Real.log w) * (1 + K / Real.log w) := by
    apply mul_lt_mul_of_pos_left _ hratio
    apply add_lt_add_right
    apply div_lt_div_of_pos_right _ hlogw
    dsimp [K]
    linarith
  change (∏ p ∈ T, (1 - (p : Real)⁻¹)⁻¹) < _
  have hfirst := hsubsetProduct.trans (by simpa [S, I, E] using hall)
  exact hfirst.trans_lt (hsmall.trans_lt hstrict)

end

end PrimesRestrictedDigits
