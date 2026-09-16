import PrimesRestrictedDigits.LatticeEstimates.ExceptionalSourceBound
import Mathlib.Tactic.GCongr

/-!
# Scalar tools for the final lattice-sum estimate

This file contains the real-power and weighted-minimum tools used in the formalization of
published Lemma 14.4.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The explicit saving used in the final lattice-sum estimate. -/
noncomputable def latticeSumSaving : Real := 127 / 21338240

theorem latticeSumSaving_pos : 0 < latticeSumSaving := by
  norm_num [latticeSumSaving]

theorem latticeSumSaving_lt_one : latticeSumSaving < 1 := by
  norm_num [latticeSumSaving]

theorem two_latticeSumSaving_lt_one_div_forty_six :
    2 * latticeSumSaving < 1 / 46 := by
  norm_num [latticeSumSaving]

theorem latticeSumSaving_le_exceptionalGap :
    latticeSumSaving <= 127 / 5334560 := by
  norm_num [latticeSumSaving]

/-- A weighted geometric mean bounds the minimum of two nonnegative reals. -/
theorem min_le_rpow_mul_rpow
    {A B s t : Real} (hA : 0 <= A) (hB : 0 <= B)
    (hs : 0 <= s) (ht : 0 <= t) (hst : s + t = 1) :
    min A B <= A ^ s * B ^ t := by
  by_cases hzero : min A B = 0
  · rw [hzero]
    exact mul_nonneg (Real.rpow_nonneg hA s) (Real.rpow_nonneg hB t)
  · have hminPos : 0 < min A B :=
      lt_of_le_of_ne (le_min hA hB) (Ne.symm hzero)
    calc
      min A B = (min A B) ^ (1 : Real) := (Real.rpow_one _).symm
      _ = (min A B) ^ (s + t) := by rw [hst]
      _ = (min A B) ^ s * (min A B) ^ t :=
        Real.rpow_add hminPos s t
      _ <= A ^ s * B ^ t :=
        mul_le_mul
          (Real.rpow_le_rpow hminPos.le (min_le_left _ _) hs)
          (Real.rpow_le_rpow hminPos.le (min_le_right _ _) ht)
          (Real.rpow_nonneg hminPos.le t)
          (Real.rpow_nonneg hA s)

/-- The one-third/two-thirds interpolation used for the common `S1` factor. -/
theorem le_rpow_one_third_mul_rpow_two_thirds
    {z A B : Real} (hz : 0 <= z) (hA : 0 <= A) (_hB : 0 <= B)
    (hzA : z <= A) (hzB : z <= B) :
    z <= A ^ (1 / 3 : Real) * B ^ (2 / 3 : Real) := by
  calc
    z = min z z := (min_self z).symm
    _ <= z ^ (1 / 3 : Real) * z ^ (2 / 3 : Real) :=
      min_le_rpow_mul_rpow hz hz (by norm_num) (by norm_num) (by norm_num)
    _ <= A ^ (1 / 3 : Real) * B ^ (2 / 3 : Real) :=
      mul_le_mul
        (Real.rpow_le_rpow hz hzA (by norm_num))
        (Real.rpow_le_rpow hz hzB (by norm_num))
        (Real.rpow_nonneg hz _) (Real.rpow_nonneg hA _)

/-- A scale quotient `R <= A*X/P`, together with `P >= X^beta`, gives the
power-scale upper bound used throughout the final exponent bookkeeping. -/
theorem latticeScale_le_mul_rpow
    {A X P R beta : Real} (hA : 0 <= A) (hX : 1 <= X)
    (hP : X ^ beta <= P) (hscale : R <= A * X / P) :
    R <= A * X ^ (1 - beta) := by
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hXPowerPos : 0 < X ^ beta := Real.rpow_pos_of_pos hXPos beta
  have hPPos : 0 < P := hXPowerPos.trans_le hP
  calc
    R <= A * X / P := hscale
    _ <= A * X / (X ^ beta) := by
      exact div_le_div_of_nonneg_left (mul_nonneg hA hXPos.le)
        hXPowerPos hP
    _ = A * X ^ (1 - beta) := by
      rw [Real.rpow_sub hXPos, Real.rpow_one]
      ring

/-- Powers of the source scale are absorbed whenever the remaining `X`
exponent is nonpositive. -/
theorem latticeScale_rpow_div_rpow_le
    {A X R beta c w : Real} (hA : 0 <= A) (hX : 1 <= X)
    (hR : 0 <= R) (hc : 0 <= c)
    (hscale : R <= A * X ^ (1 - beta))
    (hexponent : c * (1 - beta) <= w) :
    R ^ c / X ^ w <= A ^ c := by
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hpower : R ^ c <= (A * X ^ (1 - beta)) ^ c :=
    Real.rpow_le_rpow hR hscale hc
  have hdenPos : 0 < X ^ w := Real.rpow_pos_of_pos hXPos w
  calc
    R ^ c / X ^ w <= (A * X ^ (1 - beta)) ^ c / X ^ w :=
      (div_le_div_iff_of_pos_right hdenPos).2 hpower
    _ = A ^ c * ((X ^ (1 - beta)) ^ c / X ^ w) := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hXPos.le _)]
      ring
    _ = A ^ c * (X ^ ((1 - beta) * c) / X ^ w) := by
      rw [← Real.rpow_mul hXPos.le]
    _ = A ^ c * (X ^ (c * (1 - beta)) / X ^ w) :=
      congrArg (fun exponent : Real =>
        A ^ c * (X ^ exponent / X ^ w)) (mul_comm (1 - beta) c)
    _ <= A ^ c * 1 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hA c)
      apply (div_le_one hdenPos).2
      exact Real.rpow_le_rpow_of_exponent_le hX hexponent
    _ = A ^ c := mul_one _

/-- Two base-one powers are controlled by one power of their product. -/
theorem mul_rpow_le_mul_rpow_product
    {Q E u v c : Real} (hQ : 1 <= Q) (hE : 1 <= E)
    (hu : u <= c) (hv : v <= c) :
    Q ^ u * E ^ v <= (Q * E) ^ c := by
  have hQPower : Q ^ u <= Q ^ c :=
    Real.rpow_le_rpow_of_exponent_le hQ hu
  have hEPower : E ^ v <= E ^ c :=
    Real.rpow_le_rpow_of_exponent_le hE hv
  calc
    Q ^ u * E ^ v <= Q ^ c * E ^ c :=
      mul_le_mul hQPower hEPower (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
    _ = (Q * E) ^ c :=
      (Real.mul_rpow (by positivity) (by positivity)).symm

/-- Coordinatewise exponent comparison for a two-variable nonnegative
monomial whose bases are at least one. -/
theorem mul_rpow_le_mul_rpow_of_exponents
    {Q E u v u' v' : Real} (hQ : 1 <= Q) (hE : 1 <= E)
    (hu : u <= u') (hv : v <= v') :
    Q ^ u * E ^ v <= Q ^ u' * E ^ v' := by
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hQ hu)
    (Real.rpow_le_rpow_of_exponent_le hE hv)
    (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

theorem rpow_rpow_eq_mul
    {x a b : Real} (hx : 0 <= x) :
    (x ^ a) ^ b = x ^ (a * b) :=
  (Real.rpow_mul hx a b).symm

theorem pow_two_rpow
    (x exponent : Real) (hx : 0 <= x) :
    (x ^ 2) ^ exponent = x ^ (2 * exponent) := by
  calc
    (x ^ 2) ^ exponent = (x ^ (2 : Real)) ^ exponent :=
      congrArg (fun y : Real => y ^ exponent)
        (Real.rpow_natCast x 2).symm
    _ = x ^ ((2 : Real) * exponent) :=
      (Real.rpow_mul hx 2 exponent).symm

end

end PrimesRestrictedDigits
