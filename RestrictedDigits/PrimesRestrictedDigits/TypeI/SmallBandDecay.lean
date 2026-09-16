import PrimesRestrictedDigits.TypeI.SmallBandPointwise
import PrimesRestrictedDigits.TypeI.ScaleLogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic decay on the small Type I bands

This discharges the strict Lemma 8.2 denominator condition directly from the source
small-scale threshold and absorbs its explicit exponential into a logarithmic power.
-/

open scoped BigOperators
open Filter

namespace PrimesRestrictedDigits

noncomputable section

/-- Polylogarithmic Type I denominators eventually lie strictly below the
`X^(1/3)` range required by Lemma 8.2. -/
theorem exists_typeISmallDenominator_threshold (saving : Real) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      10 * Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8) <
        (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real)) := by
  let X : Nat → Real := fun length => ((10 ^ length : Nat) : Real)
  let B : Real := 4 * saving + 8
  have hX : Tendsto X atTop atTop := by
    simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10))
  have hbound :=
    ((isLittleO_log_rpow_rpow_atTop B
      (by norm_num : (0 : Real) < 1 / 3)).const_mul_left 10).bound
        (by norm_num : (0 : Real) < 1 / 2)
  have hevent : ∀ᶠ x : Real in atTop,
      10 * Real.log x ^ B < x ^ (1 / 3 : Real) := by
    filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with x hbound hx
    have hxPos : 0 < x := zero_lt_one.trans hx
    have hlogPos : 0 < Real.log x := Real.log_pos hx
    have hleft : 0 ≤ 10 * Real.log x ^ B :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hlogPos.le _)
    have hrightPos : 0 < x ^ (1 / 3 : Real) :=
      Real.rpow_pos_of_pos hxPos _
    have hbound' : 10 * Real.log x ^ B ≤
        (1 / 2 : Real) * x ^ (1 / 3 : Real) := by
      simpa only [Real.norm_of_nonneg hleft,
        Real.norm_of_nonneg hrightPos.le] using hbound
    nlinarith
  apply eventually_atTop.mp
  simpa only [X, B] using hX.eventually hevent

/-- Uniformly on `1 ≤ R ≤ log(X)^(4*A+8)`, the explicit Lemma 8.2
exponential eventually saves the source's large logarithmic power. -/
theorem exists_typeISmallBandDecay_threshold
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ R : Real, 1 ≤ R →
        R ≤ Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8) →
        typeISmallBandDecay length R ≤
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-(100 * (saving + 1))) := by
  let L : Nat → Real := fun length => Real.log (((10 ^ length : Nat) : Real))
  let B : Real := 4 * saving + 8
  let K : Real := 100 * (saving + 1)
  let c : Real := 1 / 100000000
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := by dsimp [c]; norm_num
  have hL : Tendsto L atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10))
  let epsilon : Real := c / (K * (B + 9))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hsquareAtTop : ∀ᶠ x : Real in atTop,
      ‖Real.log x ^ (2 : Real)‖ ≤ epsilon * ‖x ^ (1 : Real)‖ :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real)
      (by norm_num : (0 : Real) < 1)).bound hepsilon
  have hevent : ∀ᶠ length : Nat in atTop,
      Real.exp 1 ≤ L length ∧
        ‖Real.log (L length) ^ (2 : Real)‖ ≤
          epsilon * ‖L length ^ (1 : Real)‖ := by
    filter_upwards [hL.eventually_ge_atTop (Real.exp 1),
      hL.eventually hsquareAtTop] with length hlarge hsquare
    exact ⟨hlarge, hsquare⟩
  apply eventually_atTop.mp
  filter_upwards [hevent] with length hlength
  intro R hR hRsmall
  have hLPos : 0 < L length := (Real.exp_pos 1).trans_le hlength.1
  have hlogLOne : 1 ≤ Real.log (L length) := by
    have := Real.log_le_log (Real.exp_pos 1) hlength.1
    simpa only [Real.log_exp] using this
  have hlogLNonneg : 0 ≤ Real.log (L length) := zero_le_one.trans hlogLOne
  have hsquare : (Real.log (L length)) ^ 2 ≤ epsilon * L length := by
    simpa only [Real.rpow_two, Real.rpow_one,
      Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hLPos.le]
      using hlength.2
  have hcoefficient : 0 < K * (B + 9) := by positivity
  have hsquareScaled :
      K * (B + 9) * (Real.log (L length)) ^ 2 ≤ c * L length := by
    calc
      K * (B + 9) * (Real.log (L length)) ^ 2 ≤
          K * (B + 9) * (epsilon * L length) := by gcongr
      _ = c * L length := by
        dsimp [epsilon]
        field_simp [hcoefficient.ne']
  have htenRPos : 0 < 10 * R := by positivity
  have hRpowPos : 0 < L length ^ B := Real.rpow_pos_of_pos hLPos _
  have htenRLe : 10 * R ≤ 10 * L length ^ B := by gcongr
  have hlogTen : Real.log (10 : Real) ≤ 9 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
    norm_num at h ⊢
    exact h
  have hlogDenLe : Real.log (10 * R) ≤
      (B + 9) * Real.log (L length) := by
    calc
      Real.log (10 * R) ≤ Real.log (10 * L length ^ B) :=
        Real.log_le_log htenRPos htenRLe
      _ = Real.log 10 + B * Real.log (L length) := by
        rw [Real.log_mul (by norm_num) hRpowPos.ne', Real.log_rpow hLPos]
      _ ≤ (B + 9) * Real.log (L length) := by nlinarith
  have hlogDenPos : 0 < Real.log (10 * R) := by
    apply Real.log_pos
    nlinarith
  have hlogProduct :
      K * Real.log (L length) * Real.log (10 * R) ≤ c * L length := by
    calc
      K * Real.log (L length) * Real.log (10 * R) ≤
          K * Real.log (L length) *
            ((B + 9) * Real.log (L length)) := by gcongr
      _ = K * (B + 9) * (Real.log (L length)) ^ 2 := by ring
      _ ≤ c * L length := hsquareScaled
  have hquotient : K * Real.log (L length) ≤
      c * (L length / Real.log (10 * R)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlogDenPos).2
    simpa only [mul_assoc] using hlogProduct
  have hnegative :
      -c * (L length / Real.log (10 * R)) ≤
        -K * Real.log (L length) := by linarith
  calc
    typeISmallBandDecay length R =
        Real.exp (-c * (L length / Real.log (10 * R))) := by
      rfl
    _ ≤ Real.exp (-K * Real.log (L length)) :=
      Real.exp_le_exp.mpr hnegative
    _ = L length ^ (-K) := by
      rw [Real.rpow_def_of_pos hLPos]
      congr 1
      ring
    _ = Real.log (((10 ^ length : Nat) : Real)) ^
        (-(100 * (saving + 1))) := by rfl

/-- Every active small Type I fiber eventually reserves two logarithms for
the finite scale and harmonic aggregation. -/
theorem exists_sum_typeIDecadeFiber_div_le_smallBand
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (d : Nat) (Q R : Real),
        d ∈ Nat.divisors 10 → R ∈ typeIDecadeScalesBelow Q →
        R ≤ Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8) →
        (∑ q ∈ typeIDecadeFiber Q R,
          typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
          30 * Real.log (((10 ^ length : Nat) : Real)) ^
            (-(saving + 2)) := by
  obtain ⟨lengthDen, hden⟩ := exists_typeISmallDenominator_threshold saving
  obtain ⟨lengthDecay, hdecay⟩ :=
    exists_typeISmallBandDecay_threshold saving hsaving
  refine ⟨max 1 (max lengthDen lengthDecay), ?_⟩
  intro length hlength digit d Q R hd hR hRsmall
  have hlengthOne : 1 ≤ length := (Nat.le_max_left _ _).trans hlength
  have hlengthDen : lengthDen ≤ length :=
    (Nat.le_max_left lengthDen lengthDecay).trans
      ((Nat.le_max_right 1 (max lengthDen lengthDecay)).trans hlength)
  have hlengthDecay : lengthDecay ≤ length :=
    (Nat.le_max_right lengthDen lengthDecay).trans
      ((Nat.le_max_right 1 (max lengthDen lengthDecay)).trans hlength)
  have hRTwo := two_le_typeIDecadeScale_of_mem hR
  have hdenFiber : ∀ q ∈ typeIDecadeFiber Q R,
      ((d * q : Nat) : Real) <
        (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real)) := by
    intro q hq
    have hdLe : d ≤ 10 := Nat.divisor_le hd
    have hdLeReal : (d : Real) ≤ 10 := by exact_mod_cast hdLe
    have hqLe := (typeIDecadeFiber_data hq).2.2.2
    calc
      ((d * q : Nat) : Real) = (d : Real) * (q : Real) := by norm_num
      _ ≤ 10 * R := mul_le_mul hdLeReal hqLe (by positivity) (by positivity)
      _ ≤ 10 * Real.log (((10 ^ length : Nat) : Real)) ^
          (4 * saving + 8) := by gcongr
      _ < (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real)) :=
        hden length hlengthDen
  have hpoint := sum_typeIDecadeFiber_div_le_lInf digit length d hd hR hdenFiber
  have hdecay := hdecay length hlengthDecay R (by linarith) hRsmall
  let L : Real := Real.log (((10 ^ length : Nat) : Real))
  let B : Real := 4 * saving + 8
  let K : Real := 100 * (saving + 1)
  have hLOne : 1 ≤ L := one_le_log_typeIDecimalScale hlengthOne
  have hLPos : 0 < L := zero_lt_one.trans_le hLOne
  have hpowerNonneg : 0 ≤ L ^ (-K) := Real.rpow_nonneg hLPos.le _
  have hexponent : B + (-K) ≤ -(saving + 2) := by
    dsimp [B, K]
    nlinarith
  calc
    (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        30 * R * typeISmallBandDecay length R := hpoint
    _ ≤ 30 * R * L ^ (-K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [L, K] using hdecay
    _ ≤ 30 * L ^ B * L ^ (-K) := by
      apply mul_le_mul_of_nonneg_right _ hpowerNonneg
      apply mul_le_mul_of_nonneg_left
      · simpa only [L, B] using hRsmall
      · norm_num
    _ = 30 * (L ^ B * L ^ (-K)) := by ring
    _ = 30 * L ^ (B + (-K)) := by
      congr 1
      exact (Real.rpow_add hLPos B (-K)).symm
    _ ≤ 30 * L ^ (-(saving + 2)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hLOne hexponent) (by norm_num)
    _ = 30 * Real.log (((10 ^ length : Nat) : Real)) ^
        (-(saving + 2)) := by rfl

end

end PrimesRestrictedDigits
