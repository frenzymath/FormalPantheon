import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorption of the fundamental-sieve polynomial loss

This absorbs the fixed `delta⁻¹ ^ 17` loss produced by the elementary bounds into the rapid
error used in `MAYNARD-PRD-PUBLISHED`, p. 154 before Eq. (7.7).
-/

namespace PrimesRestrictedDigits

private theorem fundamentalErrorAbsorption_rpow
    {epsilon delta : Real} (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hscale : 4 * delta ^ (1 / 3 : Real) ≤ epsilon) :
    delta ^ (-17 : Real) * Real.exp (-epsilon / (2 * delta)) ≤
      (Nat.factorial 26 : Real) *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
  let t : Real := delta ^ (-(2 / 3 : Real))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hpoly : delta ^ (-17 : Real) ≤ t ^ (26 : Nat) := by
    calc
      delta ^ (-17 : Real) ≤ delta ^ (-(52 / 3 : Real)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
        norm_num
      _ = t ^ (26 : Nat) := by
        dsimp [t]
        rw [← Real.rpow_mul_natCast hdelta.le]
        congr 1
        norm_num
  have hdeltaMul : delta * t = delta ^ (1 / 3 : Real) := by
    calc
      delta * t = delta ^ (1 : Real) *
          delta ^ (-(2 / 3 : Real)) := by
        dsimp [t]
        rw [Real.rpow_one]
      _ = delta ^ ((1 : Real) + (-(2 / 3 : Real))) :=
        (Real.rpow_add hdelta _ _).symm
      _ = delta ^ (1 / 3 : Real) := by
        congr 1
        ring
  have hexponents : 2 * t ≤ epsilon / (2 * delta) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hdelta)]
    rw [show 2 * t * (2 * delta) = 4 * (delta * t) by ring,
      hdeltaMul]
    exact hscale
  have hexp : Real.exp (-epsilon / (2 * delta)) ≤ Real.exp (-2 * t) := by
    apply Real.exp_le_exp.mpr
    calc
      -epsilon / (2 * delta) = -(epsilon / (2 * delta)) := by ring
      _ ≤ -(2 * t) := neg_le_neg hexponents
      _ = -2 * t := by ring
  have hfactorial : 0 < (Nat.factorial 26 : Real) := by positivity
  have hpow : t ^ (26 : Nat) ≤
      (Nat.factorial 26 : Real) * Real.exp t := by
    have h := Real.pow_div_factorial_le_exp t ht.le 26
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp h
  calc
    delta ^ (-17 : Real) * Real.exp (-epsilon / (2 * delta)) ≤
        t ^ (26 : Nat) * Real.exp (-2 * t) :=
      mul_le_mul hpoly hexp (Real.exp_nonneg _) (pow_nonneg ht.le 26)
    _ ≤ ((Nat.factorial 26 : Real) * Real.exp t) *
        Real.exp (-2 * t) := by
      gcongr
    _ = (Nat.factorial 26 : Real) * Real.exp (-t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = (Nat.factorial 26 : Real) *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
      rfl

private theorem inv_pow_seventeen_eq_rpow_neg
    {delta : Real} :
    delta⁻¹ ^ (17 : Nat) = delta ^ (-17 : Real) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_neg_eq_inv_rpow delta (17 : Real)).symm

/--
Under Maynard's small-parameter reduction, the fixed polynomial loss is absorbed by the rapid
fundamental-sieve error.
-/
theorem epsilon_fourth_inv_pow
    {epsilon delta : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) (hdelta : 0 < delta)
    (hdeltaEpsilon : delta ≤ epsilon ^ (4 : Nat)) :
    delta⁻¹ ^ (17 : Nat) * Real.exp (-epsilon / (2 * delta)) ≤
      (Nat.factorial 26 : Real) *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
  have hepsilonOne : epsilon ≤ 1 := hepsilonSmall.trans (by norm_num)
  have hepsilonFourthOne : epsilon ^ (4 : Nat) ≤ 1 :=
    pow_le_one₀ hepsilon.le hepsilonOne
  have hdeltaOne : delta ≤ 1 := hdeltaEpsilon.trans hepsilonFourthOne
  have hepsilonCubeNonneg : 0 ≤ epsilon ^ (3 : Nat) := by positivity
  have hepsilonPower : epsilon ^ (4 : Nat) ≤ epsilon ^ (3 : Nat) / 64 := by
    have hmul := mul_le_mul_of_nonneg_left hepsilonSmall hepsilonCubeNonneg
    nlinarith
  have hdeltaCube : delta ≤ (epsilon / 4) ^ (3 : Nat) := by
    calc
      delta ≤ epsilon ^ (4 : Nat) := hdeltaEpsilon
      _ ≤ epsilon ^ (3 : Nat) / 64 := hepsilonPower
      _ = (epsilon / 4) ^ (3 : Nat) := by ring
  have hroot : delta ^ (1 / 3 : Real) ≤ epsilon / 4 := by
    have h := Real.rpow_le_rpow hdelta.le hdeltaCube
      (by norm_num : (0 : Real) ≤ 1 / 3)
    have hepsilonQuarter : 0 ≤ epsilon / 4 := by positivity
    have heq : ((epsilon / 4) ^ (3 : Nat)) ^ (1 / 3 : Real) =
        epsilon / 4 := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast hepsilonQuarter (by norm_num : 3 ≠ 0)
    rwa [heq] at h
  rw [inv_pow_seventeen_eq_rpow_neg]
  apply fundamentalErrorAbsorption_rpow hdelta hdeltaOne
  nlinarith

/-- Multiplication by a nonnegative mass and division by a positive logarithm
preserve the scalar absorption estimate. -/
theorem epsilon_fourth_inv_pow_mass_div_log
    {epsilon delta X mass : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) (hdelta : 0 < delta)
    (hdeltaEpsilon : delta ≤ epsilon ^ (4 : Nat))
    (hX : 1 < X) (hmass : 0 ≤ mass) :
    mass * (delta⁻¹ ^ (17 : Nat) *
        Real.exp (-epsilon / (2 * delta))) / Real.log X ≤
      (Nat.factorial 26 : Real) * mass *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X := by
  apply (div_le_div_iff_of_pos_right (Real.log_pos hX)).mpr
  have h := epsilon_fourth_inv_pow hepsilon hepsilonSmall hdelta
    hdeltaEpsilon
  calc
    mass * (delta⁻¹ ^ (17 : Nat) *
        Real.exp (-epsilon / (2 * delta))) ≤
      mass * ((Nat.factorial 26 : Real) *
        Real.exp (-(delta ^ (-(2 / 3 : Real))))) := by
      gcongr
    _ = (Nat.factorial 26 : Real) * mass *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by ring

end PrimesRestrictedDigits
