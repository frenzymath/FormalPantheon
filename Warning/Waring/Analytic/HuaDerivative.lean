import Waring.Analytic.ChenFourQuotient

/-!
# Normalized derivatives in Hua's prime-power estimate

This file defines the derivative after removal of its common coefficient
`p`-power and packages the root-complexity bound used in Hua's Lemma 1.6
[HUA1957-BOOK, pp. 5-7].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The formal derivative after removal of its maximal common coefficient
power of `p`. -/
noncomputable def huaNormalizedDerivative (p : Nat) (F : Polynomial Int) :
    Polynomial Int :=
  primePowerContentQuotient p F.derivative

/-- The normalized derivative reduced to the prime field. -/
noncomputable def huaDerivativePolynomial (p : Nat) (F : Polynomial Int) :
    Polynomial (ZMod p) :=
  (huaNormalizedDerivative p F).map (Int.castRingHom (ZMod p))

/-- The distinct roots modulo `p` of Hua's normalized derivative. -/
noncomputable def huaDerivativeRoots (p : Nat) [Fact p.Prime]
    (F : Polynomial Int) : Finset (ZMod p) :=
  (huaDerivativePolynomial p F).roots.toFinset

/-- The polynomial multiplicity of a normalized derivative root. -/
noncomputable def huaDerivativeMultiplicity (p : Nat) [Fact p.Prime]
    (F : Polynomial Int) (x : ZMod p) : Nat :=
  Polynomial.rootMultiplicity x (huaDerivativePolynomial p F)

/-- Hua's derivative-root complexity: the sum of multiplicities over the
distinct normalized derivative roots. -/
noncomputable def huaDerivativeComplexity (p : Nat) [Fact p.Prime]
    (F : Polynomial Int) : Nat :=
  ∑ x ∈ huaDerivativeRoots p F, huaDerivativeMultiplicity p F x

/-- A nonzero integer derivative remains nonzero modulo `p` after its exact
common coefficient `p`-power is removed. -/
theorem huaDerivativePolynomial_ne_zero {p : Nat} [Fact p.Prime]
    (F : Polynomial Int) (hF : F.derivative ≠ 0) :
    huaDerivativePolynomial p F ≠ 0 := by
  exact map_primePowerContentQuotient_ne_zero F.derivative hF

/-- A zero-constant integer polynomial whose reduction modulo `p` is nonzero
has a nonzero formal derivative over the integers. -/
theorem derivative_ne_zero_of_coeff_zero_of_map_ne_zero {p : Nat}
    (F : Polynomial Int) (hzero : F.coeff 0 = 0)
    (hmap : F.map (Int.castRingHom (ZMod p)) ≠ 0) :
    F.derivative ≠ 0 := by
  intro hderivative
  have hconstant := Polynomial.eq_C_of_derivative_eq_zero hderivative
  rw [hzero, Polynomial.C_0] at hconstant
  apply hmap
  rw [hconstant, Polynomial.map_zero]

/-- Nonzero reduction modulo `p` supplies an integer coefficient not
divisible by `p`. -/
theorem exists_coeff_prime_not_dvd_of_map_ne_zero {p : Nat}
    (F : Polynomial Int)
    (hmap : F.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ∃ n, ¬(p : Int) ∣ F.coeff n := by
  by_contra h
  push Not at h
  apply hmap
  ext n
  rw [Polynomial.coeff_map]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h n)

/-- Vanishing of a nonzero normalized derivative is membership in its finite
set of distinct roots. -/
theorem eval_huaDerivativePolynomial_eq_zero_iff_mem_roots {p : Nat}
    [Fact p.Prime] (F : Polynomial Int) (x : ZMod p)
    (hderivative : F.derivative ≠ 0) :
    (huaDerivativePolynomial p F).eval x = 0 ↔
      x ∈ huaDerivativeRoots p F := by
  rw [huaDerivativeRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots (huaDerivativePolynomial_ne_zero F hderivative),
    Polynomial.IsRoot.def]

/-- Every listed normalized derivative root has positive polynomial
multiplicity. -/
theorem huaDerivativeMultiplicity_pos_of_mem {p : Nat} [Fact p.Prime]
    (F : Polynomial Int) {x : ZMod p}
    (hx : x ∈ huaDerivativeRoots p F) :
    1 ≤ huaDerivativeMultiplicity p F x := by
  apply (Polynomial.rootMultiplicity_pos').2
  apply (Polynomial.mem_roots').1
  simpa [huaDerivativeRoots, huaDerivativeMultiplicity] using hx

/-- Normalizing and reducing the derivative does not exceed the usual
derivative degree bound. -/
theorem natDegree_huaDerivativePolynomial_le (p : Nat)
    (F : Polynomial Int) :
    (huaDerivativePolynomial p F).natDegree ≤ F.natDegree - 1 := by
  exact Polynomial.natDegree_map_le.trans
    ((natDegree_primePowerContentQuotient_le p F.derivative).trans
      (Polynomial.natDegree_derivative_le F))

/-- Hua's root complexity is the cardinality of the normalized derivative's
root multiset. -/
theorem huaDerivativeComplexity_eq_card_roots {p : Nat} [Fact p.Prime]
    (F : Polynomial Int) :
    huaDerivativeComplexity p F =
      (huaDerivativePolynomial p F).roots.card := by
  simpa only [huaDerivativeComplexity, huaDerivativeRoots,
    huaDerivativeMultiplicity, Polynomial.count_roots] using
      (Multiset.toFinset_sum_count_eq (huaDerivativePolynomial p F).roots)

/-- An ambient degree-five phase has normalized derivative-root complexity at
most four, in every prime characteristic. -/
theorem huaDerivativeComplexity_le_four {p : Nat} [Fact p.Prime]
    (F : Polynomial Int) (hdeg : F.natDegree ≤ 5) :
    huaDerivativeComplexity p F ≤ 4 := by
  rw [huaDerivativeComplexity_eq_card_roots]
  exact (Polynomial.card_roots' _).trans
    ((natDegree_huaDerivativePolynomial_le p F).trans (by omega))

/-- A degree-five phase primitive modulo `p` has a nonzero integer formal
derivative.  This characteristic-zero fact precedes derivative normalization;
it does not claim that the unnormalized derivative is nonzero modulo `p`. -/
theorem derivative_fifthPolynomialFormal_ne_zero_of_coefficients {p : Nat}
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0) :
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).derivative ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  intro hdegree
  have hcoeffzero (n : Nat) (hn : 0 < n) :
      (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rcases hcoeff with ha₀ | ha₁ | ha₂ | ha₃ | ha₄
  · have hzero : a₀ = 0 := by
      simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using
        hcoeffzero 5 (by omega)
    exact ha₀ (by simp [hzero])
  · have hzero : a₁ = 0 := by
      simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using
        hcoeffzero 4 (by omega)
    exact ha₁ (by simp [hzero])
  · have hzero : a₂ = 0 := by
      simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using
        hcoeffzero 3 (by omega)
    exact ha₂ (by simp [hzero])
  · have hzero : a₃ = 0 := by
      simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using
        hcoeffzero 2 (by omega)
    exact ha₃ (by simp [hzero])
  · have hzero : a₄ = 0 := by
      simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using
        hcoeffzero 1 (by omega)
    exact ha₄ (by simp [hzero])

end Waring.Analytic
