import PrimesRestrictedDigits.BasicEstimates.DivisorSubpolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial-size divisor bounds at decimal scales

This converts the global pointwise divisor estimate into the coefficient-one `X^(o(1))` form
used in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--214. The threshold is uniform in the
integer being factored.
-/

open Filter

namespace PrimesRestrictedDigits

/-- A fixed polynomial size bound can be absorbed into any positive power of
the decimal scale, uniformly in the signed factorization target. -/
theorem exists_card_int_divisorsAntidiag_le_decimalPower_rpow_threshold
    (rho K : Real) (D : Nat) (hrho : 0 < rho) (hK : 0 <= K) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall z : Int,
        (z.natAbs : Real) <=
            K * (((10 ^ length : Nat) : Real) ^ D) ->
        (z.divisorsAntidiag.card : Real) <=
          (((10 ^ length : Nat) : Real) ^ rho) := by
  let epsilon : Real := rho / (2 * ((D + 1 : Nat) : Real))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨C, hC, hglobal⟩ :=
    card_int_divisorsAntidiag_le_const_mul_rpow epsilon hepsilon
  let F : Real := C * K ^ epsilon
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hgrowth :
      Tendsto
        (fun length : Nat =>
          ((10 ^ length : Nat) : Real) ^ (rho / 2))
        atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < rho / 2)).comp hscale
  apply eventually_atTop.mp
  filter_upwards [hgrowth.eventually_ge_atTop F] with length hF
  intro z hz
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hXOne : 1 <= X := by
    dsimp [X]
    rw [Nat.cast_pow]
    exact one_le_pow₀ (by norm_num)
  have hzNonneg : (0 : Real) <= z.natAbs := by positivity
  have hzPower : (z.natAbs : Real) ^ epsilon <=
      (K * X ^ D) ^ epsilon :=
    Real.rpow_le_rpow hzNonneg (by simpa only [X] using hz) hepsilon.le
  have hDle : (D : Real) <= ((D + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ D
  have hden : 0 < 2 * ((D + 1 : Nat) : Real) := by positivity
  have hDExponent : (D : Real) * epsilon <= rho / 2 := by
    dsimp [epsilon]
    rw [mul_div]
    apply (div_le_iff₀ hden).2
    calc
      (D : Real) * rho <= ((D + 1 : Nat) : Real) * rho := by gcongr
      _ = rho / 2 * (2 * ((D + 1 : Nat) : Real)) := by ring
  have hpowerIdentity : (X ^ D) ^ epsilon =
      X ^ ((D : Real) * epsilon) := by
    rw [← Real.rpow_natCast X D]
    exact (Real.rpow_mul hX.le (D : Real) epsilon).symm
  have hfixed : F <= X ^ (rho / 2) := by
    simpa only [F, X] using hF
  calc
    (z.divisorsAntidiag.card : Real) <=
        C * (z.natAbs : Real) ^ epsilon := hglobal z
    _ <= C * (K * X ^ D) ^ epsilon :=
      mul_le_mul_of_nonneg_left hzPower hC.le
    _ = C * (K ^ epsilon * (X ^ D) ^ epsilon) := by
      rw [Real.mul_rpow hK (pow_nonneg hX.le D)]
    _ = F * X ^ ((D : Real) * epsilon) := by
      rw [hpowerIdentity]
      dsimp [F]
      ring
    _ <= F * X ^ (rho / 2) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hXOne hDExponent) (by
          dsimp [F]
          positivity)
    _ <= X ^ (rho / 2) * X ^ (rho / 2) :=
      mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hX.le _)
    _ = X ^ rho := by
      rw [← Real.rpow_add hX]
      congr 1
      ring

end PrimesRestrictedDigits
