import PrimesRestrictedDigits.Fourier.ContinuousTransform
import PrimesRestrictedDigits.Fourier.LInfOrbit
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Repaired L-infinity bound for the digit Fourier transform

This proves an explicit, uniform version of `MAYNARD-PRD-PUBLISHED`,
Lemma 10.1, pp. 169--170.  The fixed-length padded convention is intentional,
especially when the omitted digit is zero.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem normalizedPaddedDigitFourierMagnitudeAt_le_exp_sum
    (digit : Fin 10) (k : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit k theta ≤
      Real.exp (-(1 / 20 : Real) *
        ∑ i : Fin k,
          nearestIntegerDistance ((10 : Real) ^ i.val * theta) ^ 2) := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]
  calc
    (∏ i : Fin k, digitKernel digit ((10 : Real) ^ i.val * theta)) ≤
        ∏ i : Fin k, Real.exp (-(1 / 20 : Real) *
          nearestIntegerDistance ((10 : Real) ^ i.val * theta) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact digitKernel_nonneg _ _
      · intro i hi
        exact digitKernel_le_exp_sourceCoefficient _ _
    _ = Real.exp (-(1 / 20 : Real) *
        ∑ i : Fin k,
          nearestIntegerDistance ((10 : Real) ^ i.val * theta) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

/-- Explicit repaired finite form of Maynard's Lemma 10.1. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_le_exp_blockCount
    (digit : Fin 10) {k q q1 q2 : Nat} {a : Int} {eta : Real}
    (hq : q = q1 * q2) (hq2 : 0 < q2) (hq1 : 1 < q1)
    (hq10 : Nat.Coprime q1 10) (haq : Nat.Coprime a.natAbs q)
    (hqY : (q : Real) <
      (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)))
    (heta : |eta| <
      (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2) :
    normalizedPaddedDigitFourierMagnitudeAt digit k
        ((a : Real) / q + eta) ≤
      Real.exp (-(lInfBlockCount k q : Real) / 800000) := by
  let theta : Real := (a : Real) / q + eta
  let u : Nat → Real := fun i =>
    nearestIntegerDistance ((10 : Real) ^ i * theta)
  have hqNat : 0 < q := by
    have hq1pos : 0 < q1 := lt_trans Nat.zero_lt_one hq1
    simp [hq, hq1pos, hq2]
  have hstep : ∀ i : Nat, u i < 1 / 20 → u (i + 1) = 10 * u i := by
    intro i hi
    dsimp [u]
    rw [show (10 : Real) ^ (i + 1) * theta =
        10 * ((10 : Real) ^ i * theta) by rw [pow_succ']; ring]
    exact nearestIntegerDistance_ten_mul_of_lt hi
  have hlower : ∀ i : Nat, i ≤ k / 3 →
      1 / (2 * (q : Real)) < u i := by
    intro i hi
    dsimp [u, theta]
    exact nearestIntegerDistance_perturbed_rational_lower
      (by omega) hq hq2 hq1 hq10 haq hqY heta
  have hsum := lInfBlockCount_div_le_sum_sq u hqNat hstep hlower
  have hproduct := normalizedPaddedDigitFourierMagnitudeAt_le_exp_sum
    digit k theta
  calc
    normalizedPaddedDigitFourierMagnitudeAt digit k
        ((a : Real) / q + eta) ≤
        Real.exp (-(1 / 20 : Real) * ∑ i : Fin k, u i.val ^ 2) := by
      simpa [theta, u] using hproduct
    _ ≤ Real.exp (-(lInfBlockCount k q : Real) / 800000) := by
      apply Real.exp_le_exp.mpr
      nlinarith

private theorem lInfBlockLength_cast_le_logb {q : Nat} (hq : 2 ≤ q) :
    (lInfBlockLength q : Real) ≤ 9 * Real.logb 10 q := by
  have hqReal : (2 : Real) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := lt_of_lt_of_le (by norm_num) hqReal
  have hroot : (10 : Real) ^ (1 / 4 : Real) ≤ 2 := by
    rw [show (1 / 4 : Real) = (4 : Real)⁻¹ by norm_num]
    apply (Real.rpow_inv_le_iff_of_pos (x := (10 : Real)) (y := (2 : Real))
      (z := (4 : Real)) (by positivity) (by positivity) (by norm_num)).2
    norm_num [Real.rpow_natCast]
  have hquarter : (1 / 4 : Real) ≤ Real.logb 10 q := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : Real) < 10) hqPos).2
    exact hroot.trans hqReal
  have hlog : ((Nat.log 10 q : Nat) : Real) ≤ Real.logb 10 q := by
    simpa only [Nat.cast_ofNat] using Real.natLog_le_logb q 10
  rw [lInfBlockLength, Nat.cast_add, Nat.cast_ofNat]
  nlinarith

private theorem nat_div_cast_sub_one_lt (N B : Nat) (hB : 0 < B) :
    (N : Real) / B - 1 < ((N / B : Nat) : Real) := by
  have hnat : N < (N / B + 1) * B := by
    calc
      N = N % B + B * (N / B) := (Nat.mod_add_div N B).symm
      _ < B + B * (N / B) := Nat.add_lt_add_right (Nat.mod_lt N hB) _
      _ = (N / B + 1) * B := by ring
  rw [sub_lt_iff_lt_add,
    div_lt_iff₀ (by exact_mod_cast hB : (0 : Real) < B)]
  exact_mod_cast hnat

private theorem lInfBlockCount_lower {k q : Nat} (hq : 2 ≤ q) :
    (k : Real) / (27 * Real.logb 10 q) - 1 < lInfBlockCount k q := by
  let N := k / 3 + 1
  let B := lInfBlockLength q
  let L := Real.logb 10 q
  have hqPos : (1 : Real) < q := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hq)
  have hL : 0 < L := Real.logb_pos (by norm_num) hqPos
  have hB : 0 < B := by simp [B, lInfBlockLength]
  have hBReal : 0 < (B : Real) := by exact_mod_cast hB
  have hBle : (B : Real) ≤ 9 * L := by
    simpa [B, L] using lInfBlockLength_cast_le_logb hq
  have hN : (k : Real) / 3 < (N : Real) := by
    have hfloor := nat_div_cast_sub_one_lt k 3 (by norm_num)
    dsimp [N]
    push_cast
    linarith
  have hratio : (k : Real) / (27 * L) < (N : Real) / B := by
    calc
      (k : Real) / (27 * L) = ((k : Real) / 3) / (9 * L) := by ring
      _ < (N : Real) / (9 * L) :=
        (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) hL)).2 hN
      _ ≤ (N : Real) / B :=
        div_le_div₀ (by positivity) le_rfl hBReal hBle
  have hfloor := nat_div_cast_sub_one_lt N B hB
  change (k : Real) / (27 * L) - 1 < ((N / B : Nat) : Real)
  linarith

private theorem logRatio_eq {k q : Nat} (hq : 1 < q) :
    (k : Real) / Real.logb 10 q =
      Real.log (((10 ^ k : Nat) : Real)) / Real.log (q : Real) := by
  have hlogTen : Real.log (10 : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hlogQ : Real.log (q : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hq))
  rw [Real.logb, Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp

private theorem exp_neg_blockCount_le_sourceDecay {k q : Nat} (hq : 2 ≤ q) :
    Real.exp (-(lInfBlockCount k q : Real) / 800000) ≤
      3 * Real.exp (-(1 / 100000000 : Real) *
        (Real.log (((10 ^ k : Nat) : Real)) / Real.log (q : Real))) := by
  let L := Real.logb 10 q
  let T := (k : Real) / L
  have hq1 : 1 < q := lt_of_lt_of_le (by omega : 1 < 2) hq
  have hL : 0 < L :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hq1)
  have hT : 0 ≤ T := div_nonneg (by positivity) hL.le
  have hcount := lInfBlockCount_lower (k := k) hq
  have hcount' : T / 27 - 1 < (lInfBlockCount k q : Real) := by
    dsimp [T, L]
    convert hcount using 1; ring
  have hprefactor : Real.exp (1 / 800000 : Real) ≤ 3 := by
    exact (Real.exp_le_exp.mpr (by norm_num)).trans Real.exp_one_lt_three.le
  have hdecay :
      Real.exp (-(T / 21600000)) ≤ Real.exp (-(T / 100000000)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    Real.exp (-(lInfBlockCount k q : Real) / 800000) ≤
        Real.exp ((1 / 800000 : Real) - T / 21600000) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (1 / 800000 : Real) * Real.exp (-(T / 21600000)) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ 3 * Real.exp (-(T / 100000000)) :=
      mul_le_mul hprefactor hdecay (Real.exp_nonneg _) (by norm_num)
    _ = 3 * Real.exp (-(1 / 100000000 : Real) *
        (Real.log (((10 ^ k : Nat) : Real)) / Real.log (q : Real))) := by
      rw [← logRatio_eq hq1]
      dsimp [T, L]
      congr 2
      ring

/-- Source-shaped explicit form of Maynard's Lemma 10.1, with absolute
constants uniform in every digit and arithmetic parameter. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_le_sourceDecay
    (digit : Fin 10) {k q q1 q2 : Nat} {a : Int} {eta : Real}
    (hq : q = q1 * q2) (hq2 : 0 < q2) (hq1 : 1 < q1)
    (hq10 : Nat.Coprime q1 10) (haq : Nat.Coprime a.natAbs q)
    (hqY : (q : Real) <
      (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)))
    (heta : |eta| <
      (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2) :
    normalizedPaddedDigitFourierMagnitudeAt digit k
        ((a : Real) / q + eta) ≤
      3 * Real.exp (-(1 / 100000000 : Real) *
        (Real.log (((10 ^ k : Nat) : Real)) / Real.log (q : Real))) := by
  have hqTwo : 2 ≤ q := by
    have hq1Two : 2 ≤ q1 := hq1
    have hq2One : 1 ≤ q2 := hq2
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ q1 * q2 := Nat.mul_le_mul hq1Two hq2One
      _ = q := hq.symm
  exact (normalizedPaddedDigitFourierMagnitudeAt_le_exp_blockCount
    digit hq hq2 hq1 hq10 haq hqY heta).trans
      (exp_neg_blockCount_le_sourceDecay hqTwo)

end PrimesRestrictedDigits
