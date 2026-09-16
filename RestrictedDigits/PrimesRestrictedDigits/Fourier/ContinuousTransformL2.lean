import PrimesRestrictedDigits.Fourier.ContinuousPolynomialParseval
import PrimesRestrictedDigits.Fourier.ComplexTransformDerivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `L²` energy of the normalized digit transform

The complex derivative is used instead of differentiating its magnitude. This
is the repaired Parseval input for `MAYNARD-PRD-PUBLISHED`, Lemma 10.7.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Coefficient of the exact complex derivative at exponent `n`. -/
noncomputable def normalizedPaddedDigitFourierDerivativeCoefficient
    (length n : Nat) : Complex :=
  (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I) /
    (9 : Complex) ^ length

theorem normalizedPaddedDigitFourierDerivativeAt_eq_coefficient_sum
    (digit : Fin 10) (length : Nat) (t : Real) :
    normalizedPaddedDigitFourierDerivativeAt digit length t =
      ∑ n ∈ paddedRestrictedNumbers digit length,
        digitPhaseAt t n *
          (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I) /
            (9 : Complex) ^ length := by
  have hsum : HasDerivAt
      (fun x : Real =>
        (∑ n ∈ paddedRestrictedNumbers digit length, digitPhaseAt x n) /
          (9 : Complex) ^ length)
      ((∑ n ∈ paddedRestrictedNumbers digit length,
          digitPhaseAt t n *
            (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I)) /
        (9 : Complex) ^ length) t := by
    apply HasDerivAt.div_const
    apply HasDerivAt.fun_sum
    intro n hn
    exact digitPhaseAt_hasDerivAt t n
  have hactual := normalizedPaddedDigitFourierTransformAt_hasDerivAt
    digit length t
  have hsum' : HasDerivAt
      (normalizedPaddedDigitFourierTransformAt digit length)
      ((∑ n ∈ paddedRestrictedNumbers digit length,
          digitPhaseAt t n *
            (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I)) /
        (9 : Complex) ^ length) t := by
    change HasDerivAt
      (fun x : Real =>
        (∑ n ∈ paddedRestrictedNumbers digit length, digitPhaseAt x n) /
          (9 : Complex) ^ length) _ t
    exact hsum
  have heq := hactual.unique hsum'
  rw [heq]
  rw [Finset.sum_div]

theorem normalizedPaddedDigitFourierDerivativeAt_eq_polynomial_eval
    (digit : Fin 10) (length : Nat) (t : Real) :
    normalizedPaddedDigitFourierDerivativeAt digit length t =
      Polynomial.eval
        (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
        (finiteCoefficientPolynomial (paddedRestrictedNumbers digit length)
          (normalizedPaddedDigitFourierDerivativeCoefficient length)) := by
  rw [finiteCoefficientPolynomial_eval_exp]
  rw [normalizedPaddedDigitFourierDerivativeAt_eq_coefficient_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold normalizedPaddedDigitFourierDerivativeCoefficient digitPhaseAt
  rw [div_eq_mul_inv]
  ring

theorem normalizedPaddedDigitFourierDerivativeAt_integral_norm_sq
    (digit : Fin 10) (length : Nat) :
    (∫ t in (0 : Real)..1,
      ‖normalizedPaddedDigitFourierDerivativeAt digit length t‖ ^ 2) =
      ∑ n ∈ paddedRestrictedNumbers digit length,
        ‖normalizedPaddedDigitFourierDerivativeCoefficient length n‖ ^ 2 := by
  rw [show (fun t : Real =>
      ‖normalizedPaddedDigitFourierDerivativeAt digit length t‖ ^ 2) =
      (fun t : Real =>
        ‖Polynomial.eval
          (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
          (finiteCoefficientPolynomial (paddedRestrictedNumbers digit length)
            (normalizedPaddedDigitFourierDerivativeCoefficient length))‖ ^ 2) by
      funext t
      rw [normalizedPaddedDigitFourierDerivativeAt_eq_polynomial_eval]]
  exact finiteCoefficientPolynomial_integral_norm_sq_exp _ _

theorem normalizedPaddedDigitFourierDerivativeAt_integral_norm_sq_le
    (digit : Fin 10) (length : Nat) :
    (∫ t in (0 : Real)..1,
      ‖normalizedPaddedDigitFourierDerivativeAt digit length t‖ ^ 2) <=
      64 * (((10 ^ length : Nat) : Real) ^ 2) /
        (9 : Real) ^ length := by
  rw [normalizedPaddedDigitFourierDerivativeAt_integral_norm_sq]
  have hterm (n : Nat) (hn : n ∈ paddedRestrictedNumbers digit length) :
      ‖normalizedPaddedDigitFourierDerivativeCoefficient length n‖ ^ 2 <=
        64 * (((10 ^ length : Nat) : Real) ^ 2) /
          (9 : Real) ^ (2 * length) := by
    have hnlt : n < 10 ^ length :=
      (mem_paddedRestrictedNumbers.mp hn).1
    have hnY : (n : Real) <= ((10 ^ length : Nat) : Real) := by
      exact_mod_cast (Nat.le_of_lt hnlt)
    unfold normalizedPaddedDigitFourierDerivativeCoefficient
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, abs_of_nonneg]
    · norm_num only [div_pow, norm_pow, Complex.norm_ofNat]
      have hpow : (9 : Real) ^ (2 * length) =
          ((9 : Real) ^ length) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      rw [hpow]
      have hpi : Real.pi <= 4 := Real.pi_le_four
      have hnnonneg : (0 : Real) <= n := by positivity
      have hbase : (0 : Real) <= 2 * Real.pi * (n : Real) := by positivity
      have hpi2 : 2 * Real.pi <= (8 : Real) := by nlinarith
      have hupper : 2 * Real.pi * (n : Real) <=
          8 * ((10 ^ length : Nat) : Real) := by
        calc
          2 * Real.pi * (n : Real) <= 8 * (n : Real) := by
            exact mul_le_mul_of_nonneg_right hpi2 hnnonneg
          _ <= 8 * ((10 ^ length : Nat) : Real) := by
            exact mul_le_mul_of_nonneg_left hnY (by norm_num)
      have hfactor :
          (2 * Real.pi * (n : Real)) ^ 2 <=
            64 * (((10 ^ length : Nat) : Real) ^ 2) := by
        calc
          (2 * Real.pi * (n : Real)) ^ 2 <=
              (8 * ((10 ^ length : Nat) : Real)) ^ 2 :=
            (sq_le_sq₀ hbase (by positivity)).mpr hupper
          _ = 64 * (((10 ^ length : Nat) : Real) ^ 2) := by ring
      gcongr
      simpa only [mul_one] using hfactor
    · positivity
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ n ∈ paddedRestrictedNumbers digit length,
        ‖normalizedPaddedDigitFourierDerivativeCoefficient length n‖ ^ 2) <=
        ∑ _n ∈ paddedRestrictedNumbers digit length,
          64 * (((10 ^ length : Nat) : Real) ^ 2) /
            (9 : Real) ^ (2 * length) := hsum
    _ = 64 * (((10 ^ length : Nat) : Real) ^ 2) /
          (9 : Real) ^ length := by
      rw [Finset.sum_const, card_paddedRestrictedNumbers]
      norm_num [Nat.cast_pow, pow_add]
      have hpow : ((9 : Real) ^ length) ^ 2 =
          (9 : Real) ^ (2 * length) := by
        calc
          ((9 : Real) ^ length) ^ 2 = (9 : Real) ^ (length * 2) := by
            rw [pow_mul]
          _ = (9 : Real) ^ (2 * length) := by
            congr 1
            omega
      field_simp
      rw [hpow]

end

end PrimesRestrictedDigits
