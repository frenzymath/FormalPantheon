import Waring.Analytic.HuaDerivative

/-!
# Derivative content in Hua's prime-power estimate

This file defines Hua's common derivative coefficient exponent and proves the
fixed-degree estimate `p^t <= 5` [HUA1957-BOOK, pp. 5-6].
-/

namespace Waring.Analytic

/-- The exact common coefficient `p`-power exponent of an integer
polynomial's formal derivative. -/
noncomputable def huaDerivativeExponent (p : Nat) (F : Polynomial Int) : Nat :=
  padicValInt p F.derivative.content

/-- Exact factorization of a derivative into its common coefficient
`p`-power and Hua's normalized derivative. -/
theorem derivative_eq_C_pow_mul_huaNormalizedDerivative (p : Nat)
    (F : Polynomial Int) :
    F.derivative = Polynomial.C ((p : Int) ^ huaDerivativeExponent p F) *
      huaNormalizedDerivative p F := by
  exact eq_C_pow_mul_primePowerContentQuotient p F.derivative

private theorem pow_huaDerivativeExponent_dvd_of_derivative_coeff
    {p : Nat} [Fact p.Prime] (F : Polynomial Int) (n j : Nat) (a : Int)
    (hcoeff : F.derivative.coeff n = (j : Int) * a)
    (ha : (a : ZMod p) ≠ 0) :
    p ^ huaDerivativeExponent p F ∣ j := by
  let t := huaDerivativeExponent p F
  have hpInt : Prime (p : Int) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : p.Prime)
  have hnot : ¬(p : Int) ∣ a := by
    intro hdiv
    apply ha
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hdiv
  have hpowContent : (p : Int) ^ t ∣ F.derivative.content :=
    padicValInt_dvd F.derivative.content
  have hdiv : (p : Int) ^ t ∣ (j : Int) * a := by
    rw [← hcoeff]
    exact hpowContent.trans (Polynomial.content_dvd_coeff n)
  have hcoprime : IsCoprime ((p : Int) ^ t) a :=
    (hpInt.coprime_iff_not_dvd.mpr hnot).pow_left
  have hj : (p : Int) ^ t ∣ (j : Int) :=
    hcoprime.dvd_of_dvd_mul_right hdiv
  exact Int.natCast_dvd_natCast.mp
    (by simpa only [Int.natCast_pow] using hj)

/-- If some coefficient of an ambient quintic is a `p`-unit, the common
derivative coefficient power satisfies Hua's fixed-degree bound `p^t <= 5`. -/
theorem pow_huaDerivativeExponent_fifthPolynomialFormal_le_five
    {p : Nat} [Fact p.Prime] (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0) :
    p ^ huaDerivativeExponent p
        (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄) ≤ 5 := by
  let F := fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄
  rcases hcoeff with ha₀ | ha₁ | ha₂ | ha₃ | ha₄
  · have hdiv : p ^ huaDerivativeExponent p F ∣ 5 :=
      pow_huaDerivativeExponent_dvd_of_derivative_coeff F 4 5 a₀ (by
        simp [F, derivative_fifthPolynomialFormal, fifthPolynomialDerivative,
          Polynomial.coeff_monomial,
          Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]) ha₀
    exact Nat.le_of_dvd (by norm_num) hdiv
  · have hdiv : p ^ huaDerivativeExponent p F ∣ 4 :=
      pow_huaDerivativeExponent_dvd_of_derivative_coeff F 3 4 a₁ (by
        simp [F, derivative_fifthPolynomialFormal, fifthPolynomialDerivative,
          Polynomial.coeff_monomial,
          Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]) ha₁
    exact (Nat.le_of_dvd (by norm_num) hdiv).trans (by norm_num)
  · have hdiv : p ^ huaDerivativeExponent p F ∣ 3 :=
      pow_huaDerivativeExponent_dvd_of_derivative_coeff F 2 3 a₂ (by
        simp [F, derivative_fifthPolynomialFormal, fifthPolynomialDerivative,
          Polynomial.coeff_monomial,
          Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]) ha₂
    exact (Nat.le_of_dvd (by norm_num) hdiv).trans (by norm_num)
  · have hdiv : p ^ huaDerivativeExponent p F ∣ 2 :=
      pow_huaDerivativeExponent_dvd_of_derivative_coeff F 1 2 a₃ (by
        simp [F, derivative_fifthPolynomialFormal, fifthPolynomialDerivative,
          Polynomial.coeff_monomial,
          Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]) ha₃
    exact (Nat.le_of_dvd (by norm_num) hdiv).trans (by norm_num)
  · have hdiv : p ^ huaDerivativeExponent p F ∣ 1 :=
      pow_huaDerivativeExponent_dvd_of_derivative_coeff F 0 1 a₄ (by
        simp [F, derivative_fifthPolynomialFormal, fifthPolynomialDerivative,
          Polynomial.coeff_monomial,
          Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]) ha₄
    exact (Nat.le_of_dvd (by norm_num) hdiv).trans (by norm_num)

end Waring.Analytic
