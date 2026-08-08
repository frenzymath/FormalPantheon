import Waring.Analytic.HuaDerivativeRecursion

/-!
# Phase data for Hua's small-prime induction

This file packages the algebraic invariants preserved by Hua's critical
quotient recursion: zero constant term, ambient degree at most five, nonzero
reduction modulo `p`, and explicit normalized derivative data
[HUA1957-BOOK, pp. 5-7].
-/

namespace Waring.Analytic

/-- Algebraic data carried by every phase in Hua's fixed-degree induction. -/
structure HuaPhaseData (p : Nat) (F : Polynomial Int) where
  /-- The phase has no constant term. -/
  coeff_zero : F.coeff 0 = 0
  /-- Descendants remain in ambient degree at most five. -/
  natDegree_le_five : F.natDegree ≤ 5
  /-- The phase is primitive modulo `p`. -/
  map_ne_zero : F.map (Int.castRingHom (ZMod p)) ≠ 0
  /-- A chosen exact normalization of the derivative. -/
  derivativeData : HuaDerivativeData p F

/-- The normalized derivative roots attached to a Hua phase. -/
noncomputable abbrev HuaPhaseData.roots {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (phase : HuaPhaseData p F) : Finset (ZMod p) :=
  phase.derivativeData.roots

/-- Multiplicity of a normalized derivative root attached to a Hua phase. -/
noncomputable abbrev HuaPhaseData.multiplicity {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (phase : HuaPhaseData p F) (x : ZMod p) : Nat :=
  phase.derivativeData.multiplicity x

/-- Total normalized derivative-root multiplicity of a Hua phase. -/
noncomputable abbrev HuaPhaseData.complexity {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (phase : HuaPhaseData p F) : Nat :=
  phase.derivativeData.complexity

/-- Every Hua phase has a nonzero integer derivative. -/
theorem HuaPhaseData.derivative_ne_zero {p : Nat} [Fact p.Prime]
    {F : Polynomial Int} (phase : HuaPhaseData p F) :
    F.derivative ≠ 0 := by
  intro hzero
  have hfactor := phase.derivativeData.derivative_eq
  rw [hzero] at hfactor
  have hpne : (p : Int) ^ phase.derivativeData.exponent ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hCne :
      Polynomial.C ((p : Int) ^ phase.derivativeData.exponent) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hpne
  have hnormalized : phase.derivativeData.normalized = 0 := by
    exact (mul_eq_zero.mp hfactor.symm).resolve_left hCne
  apply phase.derivativeData.map_normalized_ne_zero
  rw [hnormalized, Polynomial.map_zero]

/-- The critical scaled Taylor difference of a Hua phase is nonzero. -/
theorem HuaPhaseData.scaledTaylorDifference_ne_zero
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) (x : Int) :
    scaledTaylorDifference (p : Int) x F ≠ 0 := by
  have htranslated : huaScaledTranslate p x F.derivative ≠ 0 :=
    huaScaledTranslate_ne_zero x F.derivative phase.derivative_ne_zero
  have hpC : Polynomial.C (p : Int) ≠ 0 := by
    apply Polynomial.C_ne_zero.mpr
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hderivative :
      (scaledTaylorDifference (p : Int) x F).derivative ≠ 0 := by
    rw [derivative_scaledTaylorDifference_eq_C_mul_huaScaledTranslate]
    exact mul_ne_zero hpC htranslated
  intro hzero
  apply hderivative
  rw [hzero, Polynomial.derivative_zero]

/-- The extracted derivative power of every ambient degree-five Hua phase is
at most five.  This applies to recursive child phases as well as the initial
formal quintic. -/
theorem HuaPhaseData.pow_derivativeExponent_le_five
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) :
    p ^ phase.derivativeData.exponent ≤ 5 := by
  obtain ⟨n, hn⟩ :=
    exists_coeff_prime_not_dvd_of_map_ne_zero F phase.map_ne_zero
  have hnpos : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    apply hn
    rw [hnzero, phase.coeff_zero]
    exact dvd_zero _
  have hcoeffNe : F.coeff n ≠ 0 := by
    intro hzero
    apply hn
    rw [hzero]
    exact dvd_zero _
  have hnle : n ≤ 5 :=
    (Polynomial.le_natDegree_of_ne_zero hcoeffNe).trans
      phase.natDegree_le_five
  have hcoeff := congrArg
    (fun A : Polynomial Int ↦ A.coeff (n - 1))
    phase.derivativeData.derivative_eq
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul] at hcoeff
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  rw [hindex] at hcoeff
  have hcastIndex : ((n - 1 : Nat) : Int) + 1 = n := by
    exact_mod_cast hindex
  rw [hcastIndex] at hcoeff
  have hdiv : (p : Int) ^ phase.derivativeData.exponent ∣
      (n : Int) * F.coeff n := by
    refine ⟨phase.derivativeData.normalized.coeff (n - 1), ?_⟩
    rw [← hcoeff]
    ring
  have hpInt : Prime (p : Int) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : p.Prime)
  have hcoprime : IsCoprime
      ((p : Int) ^ phase.derivativeData.exponent) (F.coeff n) :=
    (hpInt.coprime_iff_not_dvd.mpr hn).pow_left
  have hnDiv : (p : Int) ^ phase.derivativeData.exponent ∣ (n : Int) :=
    hcoprime.dvd_of_dvd_mul_right (by
      simpa [mul_comm] using hdiv)
  have hnDivNat : p ^ phase.derivativeData.exponent ∣ n :=
    Int.natCast_dvd_natCast.mp (by
      simpa only [Int.natCast_pow] using hnDiv)
  exact (Nat.le_of_dvd hnpos hnDivNat).trans hnle

/-- Every degree-five Hua phase has total normalized derivative-root
complexity at most four, independently of the chosen exact normalization. -/
theorem HuaPhaseData.complexity_le_four
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) : phase.complexity ≤ 4 := by
  let d := phase.derivativeData
  have hpne : (p : Int) ^ d.exponent ≠ 0 := by
    exact pow_ne_zero _ (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hdegree : F.derivative.natDegree = d.normalized.natDegree := by
    have h := congrArg Polynomial.natDegree d.derivative_eq
    simpa only [Polynomial.natDegree_C_mul hpne] using h
  have hfour : F.natDegree - 1 ≤ 4 := by
    have hdeg := phase.natDegree_le_five
    omega
  exact d.complexity_le_natDegree.trans
    (Polynomial.natDegree_map_le.trans
      (hdegree.symm.le.trans
        ((Polynomial.natDegree_derivative_le F).trans hfour)))

/-- The reduction of a formal quintic is nonzero if one of its five
coefficients is nonzero modulo `p`. -/
theorem map_fifthPolynomialFormal_ne_zero_of_coefficients {p : Nat}
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0) :
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).map
        (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  rcases hcoeff with ha₀ | ha₁ | ha₂ | ha₃ | ha₄
  · apply ha₀
    have h := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff 5) hzero
    simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using h
  · apply ha₁
    have h := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff 4) hzero
    simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using h
  · apply ha₂
    have h := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff 3) hzero
    simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using h
  · apply ha₃
    have h := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff 2) hzero
    simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using h
  · apply ha₄
    have h := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff 1) hzero
    simpa [fifthPolynomialFormal, Polynomial.coeff_monomial] using h

/-- The initial primitive quintic carries canonical Hua phase data. -/
noncomputable def fifthPolynomialHuaPhaseData
    {p : Nat} [Fact p.Prime] (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0) :
    HuaPhaseData p (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄) := by
  let F := fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄
  have hmap : F.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_fifthPolynomialFormal_ne_zero_of_coefficients
      a₀ a₁ a₂ a₃ a₄ hcoeff
  have hderivative : F.derivative ≠ 0 :=
    derivative_fifthPolynomialFormal_ne_zero_of_coefficients
      a₀ a₁ a₂ a₃ a₄ hcoeff
  exact
    { coeff_zero := by simp [fifthPolynomialFormal]
      natDegree_le_five :=
        natDegree_fifthPolynomialFormal_le_five a₀ a₁ a₂ a₃ a₄
      map_ne_zero := hmap
      derivativeData := canonicalHuaDerivativeData F hderivative }

end Waring.Analytic
