import PrimesRestrictedDigits.Fourier.ContinuousTransform
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous Parseval for finite exponential polynomials

This module supplies the repaired `L²` identity used by the alternative
hybrid estimate. The polynomial carrier is finite and its coefficients may
vary with the exponent, so the same bridge also supports the derivative
energy. The source is `MAYNARD-PRD-PUBLISHED`, Lemma 10.7, pp. 180--184;
the printed endpoint and norm-derivative statements are not reused.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The polynomial with the prescribed finite coefficient list. -/
noncomputable def finiteCoefficientPolynomial
    (support : Finset Nat) (coeff : Nat -> Complex) : Polynomial Complex :=
  ∑ n ∈ support, Polynomial.monomial n (coeff n)

theorem finiteCoefficientPolynomial_coeff
    (support : Finset Nat) (coeff : Nat -> Complex) (m : Nat) :
    (finiteCoefficientPolynomial support coeff).coeff m =
      if m ∈ support then coeff m else 0 := by
  classical
  simp [finiteCoefficientPolynomial,
    Polynomial.coeff_monomial, eq_comm]

theorem finiteCoefficientPolynomial_support
    (support : Finset Nat) (coeff : Nat -> Complex) :
    (finiteCoefficientPolynomial support coeff).support =
      support.filter fun n => coeff n ≠ 0 := by
  classical
  ext m
  rw [Polynomial.mem_support_iff, finiteCoefficientPolynomial_coeff]
  by_cases hm : m ∈ support <;> simp [hm]

/-- Polynomial Parseval, with zero coefficients on the chosen finite carrier
    harmlessly retained in the right-hand sum. -/
theorem finiteCoefficientPolynomial_circleAverage_norm_sq
    (support : Finset Nat) (coeff : Nat -> Complex) :
    Real.circleAverage
        (fun z : Complex => ‖Polynomial.eval z
          (finiteCoefficientPolynomial support coeff)‖ ^ 2) 0 1 =
      ∑ n ∈ support, ‖coeff n‖ ^ 2 := by
  have hp := Polynomial.sum_sq_norm_coeff_eq_circleAverage
    (finiteCoefficientPolynomial support coeff)
  rw [finiteCoefficientPolynomial_support] at hp
  rw [← hp]
  simp_rw [finiteCoefficientPolynomial_coeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : coeff n = 0 <;> simp [hn, hc]

theorem finiteCoefficientPolynomial_eval_exp
    (support : Finset Nat) (coeff : Nat -> Complex) (t : Real) :
    Polynomial.eval (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
        (finiteCoefficientPolynomial support coeff) =
      ∑ n ∈ support, coeff n *
        Complex.exp (((2 * Real.pi * (n : Real) * t : Real) : Complex) * Complex.I) := by
  classical
  simp only [finiteCoefficientPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Circle-average Parseval rewritten as an integral on the source's unit
    interval. -/
theorem finiteCoefficientPolynomial_integral_norm_sq_exp
    (support : Finset Nat) (coeff : Nat -> Complex) :
    (∫ t in (0 : Real)..1,
      ‖Polynomial.eval
        (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
        (finiteCoefficientPolynomial support coeff)‖ ^ 2) =
      ∑ n ∈ support, ‖coeff n‖ ^ 2 := by
  have hcircle := finiteCoefficientPolynomial_circleAverage_norm_sq support coeff
  rw [Real.circleAverage_def] at hcircle
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun phi : Real =>
      ‖Polynomial.eval (Complex.exp (((phi : Real) : Complex) * Complex.I))
        (finiteCoefficientPolynomial support coeff)‖ ^ 2)
    (2 * Real.pi) (a := (0 : Real)) (b := 1)
  have hpi : (2 * Real.pi : Real) ≠ 0 := by positivity
  norm_num only [mul_zero, mul_one] at hchange
  rw [show (fun phi : Real =>
      ‖Polynomial.eval (circleMap 0 1 phi)
        (finiteCoefficientPolynomial support coeff)‖ ^ 2) =
      (fun phi : Real =>
        ‖Polynomial.eval (Complex.exp (((phi : Real) : Complex) * Complex.I))
          (finiteCoefficientPolynomial support coeff)‖ ^ 2) by
        funext phi
        simp [circleMap]] at hcircle
  have hscaled :
      (2 * Real.pi)⁻¹ •
          ∫ phi in (0 : Real)..2 * Real.pi,
            ‖Polynomial.eval (Complex.exp (((phi : Real) : Complex) * Complex.I))
              (finiteCoefficientPolynomial support coeff)‖ ^ 2 =
        ∫ t in (0 : Real)..1,
          ‖Polynomial.eval
            (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
            (finiteCoefficientPolynomial support coeff)‖ ^ 2 := by
    rw [← hchange]
    simp only [smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  rw [hscaled] at hcircle
  exact hcircle

theorem normalizedPaddedDigitFourierTransformAt_eq_polynomial_eval
    (digit : Fin 10) (length : Nat) (t : Real) :
    normalizedPaddedDigitFourierTransformAt digit length t =
      Polynomial.eval
        (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
        (finiteCoefficientPolynomial (paddedRestrictedNumbers digit length)
          (fun _ => ((9 : Complex) ^ length)⁻¹)) := by
  rw [finiteCoefficientPolynomial_eval_exp]
  unfold normalizedPaddedDigitFourierTransformAt paddedDigitFourierSumAt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  unfold digitPhaseAt
  rw [div_eq_mul_inv]
  have hphase :
      Complex.exp (↑(2 * Real.pi * (n : Real) * t) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * (n : Nat) * t) * Complex.I) := by
    rfl
  rw [hphase]
  ring

theorem normalizedPaddedDigitFourierTransformAt_integral_norm_sq
    (digit : Fin 10) (length : Nat) :
    (∫ t in (0 : Real)..1,
      ‖normalizedPaddedDigitFourierTransformAt digit length t‖ ^ 2) =
      1 / (9 : Real) ^ length := by
  rw [show (fun t : Real =>
      ‖normalizedPaddedDigitFourierTransformAt digit length t‖ ^ 2) =
      (fun t : Real =>
        ‖Polynomial.eval
          (Complex.exp (((2 * Real.pi * t : Real) : Complex) * Complex.I))
          (finiteCoefficientPolynomial (paddedRestrictedNumbers digit length)
            (fun _ => ((9 : Complex) ^ length)⁻¹))‖ ^ 2) by
      funext t
      rw [normalizedPaddedDigitFourierTransformAt_eq_polynomial_eval]]
  rw [finiteCoefficientPolynomial_integral_norm_sq_exp]
  rw [Finset.sum_const, card_paddedRestrictedNumbers]
  simp only [nsmul_eq_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  norm_num [Nat.cast_pow]
  field_simp

theorem normalizedPaddedDigitFourierMagnitudeAt_integral_sq
    (digit : Fin 10) (length : Nat) :
    (∫ t in (0 : Real)..1,
      normalizedPaddedDigitFourierMagnitudeAt digit length t ^ 2) =
      1 / (9 : Real) ^ length := by
  simpa only [norm_normalizedPaddedDigitFourierTransformAt] using
    normalizedPaddedDigitFourierTransformAt_integral_norm_sq digit length

end

end PrimesRestrictedDigits
