import Waring.Analytic.PolynomialSums

/-!
# Completion of incomplete fifth-power sums

This file proves the exact finite Fourier-completion identity in Chen's
Lemma 6 [CHEN1964-EN, p. 1551, equation (8)].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Fifth-power character sum over the integer interval `M < x ≤ M+m`. -/
noncomputable def shortPowerSum {q : Nat} [NeZero q] (a : ZMod q)
    (M : Int) (m : Nat) : Complex :=
  ∑ x ∈ Finset.Ioc M (M + m), ZMod.stdAddChar (a * (x : ZMod q) ^ 5)

/-- Fourier coefficient of the interval `M < x ≤ M+m`, with the negative
sign paired with the positive linear term in the completed polynomial. -/
noncomputable def intervalFourierCoefficient {q : Nat} [NeZero q]
    (M : Int) (m : Nat) (h : ZMod q) : Complex :=
  ∑ x ∈ Finset.Ioc M (M + m), ZMod.stdAddChar (-(h * (x : ZMod q)))

private lemma sum_frequency_mul_polynomialCompleteSum {q : Nat} [NeZero q]
    (a : ZMod q) (x : Int) :
    ∑ h : ZMod q, ZMod.stdAddChar (-(h * (x : ZMod q))) *
        polynomialCompleteSum a 0 0 0 h =
      (q : Complex) * ZMod.stdAddChar (a * (x : ZMod q) ^ 5) := by
  simp_rw [polynomialCompleteSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ y : ZMod q, ∑ h : ZMod q,
        ZMod.stdAddChar (-(h * (x : ZMod q))) *
          ZMod.stdAddChar (fifthPolynomial a 0 0 0 h y) =
        ∑ y : ZMod q, ZMod.stdAddChar (a * y ^ 5) *
          ∑ h : ZMod q, ZMod.stdAddChar (h * (y - (x : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      calc
        ZMod.stdAddChar (-(h * (x : ZMod q))) *
            ZMod.stdAddChar (fifthPolynomial a 0 0 0 h y) =
            ZMod.stdAddChar
              (-(h * (x : ZMod q)) + fifthPolynomial a 0 0 0 h y) := by
          rw [ZMod.stdAddChar.map_add_eq_mul]
        _ = ZMod.stdAddChar (a * y ^ 5 + h * (y - (x : ZMod q))) := by
          congr 1
          simp only [fifthPolynomial]
          ring
        _ = ZMod.stdAddChar (a * y ^ 5) *
            ZMod.stdAddChar (h * (y - (x : ZMod q))) :=
          ZMod.stdAddChar.map_add_eq_mul _ _
    _ = ∑ y : ZMod q, ZMod.stdAddChar (a * y ^ 5) *
          (if y - (x : ZMod q) = 0 then q else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [sum_stdAddChar_mul]
    _ = (q : Complex) * ZMod.stdAddChar (a * (x : ZMod q) ^ 5) := by
      simp only [sub_eq_zero]
      simp
      ring

/-- Exact completion of an interval fifth-power sum into complete polynomial
sums with a varying linear coefficient. -/
theorem shortPowerSum_eq_complete (q : Nat) [NeZero q] (a : ZMod q)
    (M : Int) (m : Nat) :
    shortPowerSum a M m =
      (q : Complex)⁻¹ * ∑ h : ZMod q,
        intervalFourierCoefficient M m h *
          polynomialCompleteSum a 0 0 0 h := by
  unfold shortPowerSum intervalFourierCoefficient
  symm
  calc
    (q : Complex)⁻¹ * ∑ h : ZMod q,
        (∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(h * (x : ZMod q)))) *
          polynomialCompleteSum a 0 0 0 h =
        (q : Complex)⁻¹ * ∑ h : ZMod q,
          ∑ x ∈ Finset.Ioc M (M + m),
            ZMod.stdAddChar (-(h * (x : ZMod q))) *
              polynomialCompleteSum a 0 0 0 h := by
      simp_rw [Finset.sum_mul]
    _ = (q : Complex)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
          ∑ h : ZMod q, ZMod.stdAddChar (-(h * (x : ZMod q))) *
            polynomialCompleteSum a 0 0 0 h := by
      congr 1
      rw [Finset.sum_comm]
    _ = (q : Complex)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
          (q : Complex) * ZMod.stdAddChar (a * (x : ZMod q) ^ 5) := by
      apply congrArg ((q : Complex)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro x _
      exact sum_frequency_mul_polynomialCompleteSum a x
    _ = ∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (a * (x : ZMod q) ^ 5) := by
      rw [← Finset.mul_sum]
      have hq : (q : Complex) ≠ 0 := by exact_mod_cast NeZero.ne q
      rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- A uniform bound for the completed polynomial sums reduces an incomplete
sum to the `L1` norm of its interval Fourier coefficients. -/
theorem norm_shortPowerSum_le (q : Nat) [NeZero q] (a : ZMod q)
    (M : Int) (m : Nat) (B : Real)
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖shortPowerSum a M m‖ ≤
      (q : Real)⁻¹ *
        (∑ h : ZMod q, ‖intervalFourierCoefficient M m h‖) * B := by
  rw [shortPowerSum_eq_complete q]
  calc
    ‖(q : Complex)⁻¹ * ∑ h : ZMod q,
        intervalFourierCoefficient M m h *
          polynomialCompleteSum a 0 0 0 h‖ =
        (q : Real)⁻¹ * ‖∑ h : ZMod q,
          intervalFourierCoefficient M m h *
            polynomialCompleteSum a 0 0 0 h‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (q : Real)⁻¹ * ∑ h : ZMod q,
          ‖intervalFourierCoefficient M m h *
            polynomialCompleteSum a 0 0 0 h‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (q : Real)⁻¹ * ∑ h : ZMod q,
          ‖intervalFourierCoefficient M m h‖ *
            ‖polynomialCompleteSum a 0 0 0 h‖ := by
      simp only [norm_mul]
    _ ≤ (q : Real)⁻¹ * ∑ h : ZMod q,
          ‖intervalFourierCoefficient M m h‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun h _ ↦
        mul_le_mul_of_nonneg_left (hcomplete h) (norm_nonneg _)
    _ = (q : Real)⁻¹ *
        (∑ h : ZMod q, ‖intervalFourierCoefficient M m h‖) * B := by
      rw [← Finset.sum_mul]
      ring

end Waring.Analytic
