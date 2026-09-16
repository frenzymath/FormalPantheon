import Waring.Analytic.ChenFourCriticalBlocks
import Waring.Analytic.ChenFourValuation

/-!
# Primitive quotients and periodic critical blocks in Chen's Lemma 4

This file formalizes the common-prime-power quotient and repetition step in
Chen's prime-power induction [CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Remove the maximal common power of `p` from an integer polynomial via its
canonical content/primitive-part factorization. -/
noncomputable def primePowerContentQuotient (p : Nat) (F : Polynomial Int) :
    Polynomial Int :=
  Polynomial.C
      (F.content / (p : Int) ^ padicValInt p F.content) *
    F.primPart

/-- Chen's common content exponent at a translated critical block. -/
noncomputable def fifthCriticalExponent (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) : Nat :=
  padicValInt p (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content

/-- The translated critical quintic after removing its maximal common
`p`-power. -/
noncomputable def fifthCriticalQuotient (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) : Polynomial Int :=
  primePowerContentQuotient p
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄)

/-- The original polynomial is its maximal common `p`-power times the
canonical quotient. -/
theorem eq_C_pow_mul_primePowerContentQuotient (p : Nat)
    (F : Polynomial Int) :
    F = Polynomial.C ((p : Int) ^ padicValInt p F.content) *
      primePowerContentQuotient p F := by
  change F = Polynomial.C ((p : Int) ^ padicValInt p F.content) *
    (Polynomial.C
        (F.content / (p : Int) ^ padicValInt p F.content) * F.primPart)
  have hdiv : (p : Int) ^ padicValInt p F.content ∣ F.content :=
    padicValInt_dvd F.content
  have hcontent : F.content =
      (p : Int) ^ padicValInt p F.content *
        (F.content / (p : Int) ^ padicValInt p F.content) := by
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hdiv).symm
  calc
    F = Polynomial.C F.content * F.primPart :=
      F.eq_C_content_mul_primPart
    _ = Polynomial.C
          ((p : Int) ^ padicValInt p F.content *
            (F.content / (p : Int) ^ padicValInt p F.content)) *
          F.primPart := congrArg (fun c : Int ↦ Polynomial.C c * F.primPart)
            hcontent
    _ = Polynomial.C ((p : Int) ^ padicValInt p F.content) *
        (Polynomial.C
          (F.content / (p : Int) ^ padicValInt p F.content) * F.primPart) := by
      simp only [map_mul]
      ring

/-- After removing the maximal common `p`-power from a nonzero polynomial,
the quotient content is not divisible by `p`. -/
theorem prime_not_dvd_content_primePowerContentQuotient {p : Nat}
    [Fact p.Prime] (F : Polynomial Int) (hF : F ≠ 0) :
    ¬(p : Int) ∣ (primePowerContentQuotient p F).content := by
  let sigma := padicValInt p F.content
  let c := F.content / (p : Int) ^ sigma
  have hcontent : F.content = (p : Int) ^ sigma * c := by
    have hdiv : (p : Int) ^ sigma ∣ F.content := padicValInt_dvd F.content
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hdiv).symm
  have hcontent_ne : F.content ≠ 0 :=
    Polynomial.content_eq_zero_iff.not.mpr hF
  have hc : ¬(p : Int) ∣ c := by
    intro hpc
    rcases hpc with ⟨z, hz⟩
    have hpow : (p : Int) ^ (sigma + 1) ∣ F.content := by
      refine ⟨z, ?_⟩
      rw [hcontent, hz, pow_succ]
      ring
    rcases (padicValInt_dvd_iff (p := p) (sigma + 1) F.content).mp hpow with
      hzero | hle
    · exact hcontent_ne hzero
    · omega
  rw [primePowerContentQuotient, Polynomial.content_C_mul,
    Polynomial.content_primPart, mul_one, dvd_normalize_iff]
  exact hc

/-- If a prime does not divide the content, reduction of the polynomial
modulo that prime is nonzero. -/
theorem map_intCast_ne_zero_of_prime_not_dvd_content {p : Nat}
    [Fact p.Prime] (F : Polynomial Int) (hcontent : ¬(p : Int) ∣ F.content) :
    F.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hmap
  apply hcontent
  rw [Polynomial.dvd_content_iff_C_dvd,
    Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcoeff := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff n) hmap
  simpa using hcoeff

/-- The canonical quotient of a nonzero polynomial remains nonzero after
reduction modulo `p`. -/
theorem map_primePowerContentQuotient_ne_zero {p : Nat} [Fact p.Prime]
    (F : Polynomial Int) (hF : F ≠ 0) :
    (primePowerContentQuotient p F).map
        (Int.castRingHom (ZMod p)) ≠ 0 :=
  map_intCast_ne_zero_of_prime_not_dvd_content _
    (prime_not_dvd_content_primePowerContentQuotient F hF)

/-- Removing the maximal common prime power does not increase natural
degree. -/
theorem natDegree_primePowerContentQuotient_le (p : Nat)
    (F : Polynomial Int) :
    (primePowerContentQuotient p F).natDegree ≤ F.natDegree := by
  unfold primePowerContentQuotient
  exact (Polynomial.natDegree_C_mul_le _ _).trans_eq
    (Polynomial.natDegree_primPart F)

/-- Under Chen's primitive coefficient hypothesis, every critical translate
is a nonzero integer polynomial. -/
theorem fifthCriticalTranslate_ne_zero {p : Nat} [Fact p.Prime]
    (hp : 11 ≤ p) (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ ≠ 0 := by
  intro hzero
  let m := fifthDerivativeMultiplicity
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
    (a₃ : ZMod p) (a₄ : ZMod p) (x : ZMod p)
  have hcoeffzero := congrArg
    (fun F : Polynomial Int ↦ F.coeff (m + 1)) hzero
  apply prime_pow_succ_multiplicity_not_dvd_coeff_fifthCriticalTranslate
    hp x a₀ a₁ a₂ a₃ a₄ hcoeff
  simp [m, hcoeffzero]

/-- Chen's canonical critical exponent lies between two and derivative-root
multiplicity plus one. -/
theorem fifthCriticalExponent_mem_interval {p : Nat} [Fact p.Prime]
    (hp : 11 ≤ p) (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    2 ≤ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄ ∧
      fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄ ≤
        fifthDerivativeMultiplicity
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p) (x : ZMod p) + 1 := by
  exact padicValInt_content_fifthCriticalTranslate_mem_interval
    hp x a₀ a₁ a₂ a₃ a₄ hcoeff hroot

/-- Exact factorization of a translated critical quintic by its canonical
common prime power. -/
theorem fifthCriticalTranslate_eq_C_pow_mul_fifthCriticalQuotient
    (p : Nat) (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) :
    fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ =
      Polynomial.C
          ((p : Int) ^ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄) *
        fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄ := by
  exact eq_C_pow_mul_primePowerContentQuotient p
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄)

/-- The critical quotient remains a nonzero polynomial modulo `p`. -/
theorem map_fifthCriticalQuotient_ne_zero {p : Nat} [Fact p.Prime]
    (hp : 11 ≤ p) (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    (fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).map
        (Int.castRingHom (ZMod p)) ≠ 0 := by
  exact map_primePowerContentQuotient_ne_zero _
    (fifthCriticalTranslate_ne_zero hp x a₀ a₁ a₂ a₃ a₄ hcoeff)

/-- The critical quotient still has degree at most five. -/
theorem natDegree_fifthCriticalQuotient_le_five (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    (fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).natDegree ≤ 5 :=
  (natDegree_primePowerContentQuotient_le p _).trans
    (natDegree_fifthCriticalTranslate_le_five p x a₀ a₁ a₂ a₃ a₄)

/-- Dividing out the common prime power preserves the zero constant term. -/
theorem coeff_zero_fifthCriticalQuotient {p : Nat} [Fact p.Prime]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) :
    (fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 0 = 0 := by
  have hpne : (p : Int) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq := congrArg (fun F : Polynomial Int ↦ F.coeff 0)
    (fifthCriticalTranslate_eq_C_pow_mul_fifthCriticalQuotient
      p x a₀ a₁ a₂ a₃ a₄)
  rw [coeff_zero_fifthCriticalTranslate, Polynomial.coeff_C_mul] at heq
  have hmul :
      (p : Int) ^ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄ *
        (fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 0 = 0 := by
    exact heq.symm
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hpne)

/-- A critical quotient is exactly the source's five-term polynomial formed
from its positive coefficients. -/
theorem fifthCriticalQuotient_eq_fifthPolynomialFormal_coefficients
    {p : Nat} [Fact p.Prime] (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) :
    fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄ =
      fifthPolynomialFormal
        ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 5)
        ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 4)
        ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 3)
        ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 2)
        ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 1) := by
  let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
  have hdegree : G.natDegree ≤ 5 :=
    natDegree_fifthCriticalQuotient_le_five p x a₀ a₁ a₂ a₃ a₄
  have hzero : G.coeff 0 = 0 :=
    coeff_zero_fifthCriticalQuotient x a₀ a₁ a₂ a₃ a₄
  change G = fifthPolynomialFormal
    (G.coeff 5) (G.coeff 4) (G.coeff 3) (G.coeff 2) (G.coeff 1)
  ext n
  by_cases hn : n ≤ 5
  · interval_cases n <;>
      simp [fifthPolynomialFormal, hzero, Polynomial.coeff_monomial]
  · have hcoeff : G.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (hdegree.trans_lt (Nat.lt_of_not_ge hn))
    simp [fifthPolynomialFormal, hcoeff, Polynomial.coeff_monomial,
      show 5 ≠ n by omega, show 4 ≠ n by omega, show 3 ≠ n by omega,
      show 2 ≠ n by omega, show 1 ≠ n by omega]

/-- The five positive coefficients extracted from a critical quotient are
primitive modulo `p`. -/
theorem fifthCriticalQuotient_coefficients_primitive {p : Nat}
    [Fact p.Prime] (hp : 11 ≤ p) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
    (G.coeff 5 : ZMod p) ≠ 0 ∨ (G.coeff 4 : ZMod p) ≠ 0 ∨
      (G.coeff 3 : ZMod p) ≠ 0 ∨ (G.coeff 2 : ZMod p) ≠ 0 ∨
      (G.coeff 1 : ZMod p) ≠ 0 := by
  dsimp only
  let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
  have hmap : G.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_fifthCriticalQuotient_ne_zero hp x a₀ a₁ a₂ a₃ a₄ hcoeff
  by_contra hzero
  push Not at hzero
  apply hmap
  change (fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).map
    (Int.castRingHom (ZMod p)) = 0
  rw [fifthCriticalQuotient_eq_fifthPolynomialFormal_coefficients]
  ext n
  simp [fifthPolynomialFormal,
    hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2.1,
    hzero.2.2.2.2]

/-- The complete finite sum of a critical quotient is the five-coefficient
complete polynomial sum used by the induction hypothesis. -/
theorem sum_fifthCriticalQuotient_eq_integerPolynomialCompleteSum
    {p r : Nat} [Fact p.Prime] [NeZero r]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) :
    let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
    (∑ y : Fin r,
        ZMod.stdAddChar ((G.eval (y.val : Int) : Int) : ZMod r)) =
      integerPolynomialCompleteSum (q := r)
        (G.coeff 5) (G.coeff 4) (G.coeff 3) (G.coeff 2) (G.coeff 1) := by
  dsimp only
  let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
  rw [integerPolynomialCompleteSum, polynomialCompleteSum]
  rw [← (ZMod.finEquiv r).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg ZMod.stdAddChar
  rw [show (ZMod.finEquiv r).toEquiv y = ((y.val : Nat) : ZMod r) by
    change ZMod.finEquiv r y = _
    exact zmod_finEquiv_apply y]
  have hG : G = fifthPolynomialFormal
      (G.coeff 5) (G.coeff 4) (G.coeff 3) (G.coeff 2) (G.coeff 1) := by
    simpa only [G] using
      fifthCriticalQuotient_eq_fifthPolynomialFormal_coefficients
        (p := p) x a₀ a₁ a₂ a₃ a₄
  change ((G.eval (y.val : Int) : Int) : ZMod r) = _
  calc
    ((G.eval (y.val : Int) : Int) : ZMod r) =
        (((fifthPolynomialFormal
          (G.coeff 5) (G.coeff 4) (G.coeff 3)
          (G.coeff 2) (G.coeff 1)).eval (y.val : Int) : Int) : ZMod r) :=
      congrArg (fun z : Int ↦ (z : ZMod r))
        (congrArg (fun F : Polynomial Int ↦ F.eval (y.val : Int)) hG)
    _ = fifthPolynomial
        (G.coeff 5 : ZMod r) (G.coeff 4 : ZMod r)
        (G.coeff 3 : ZMod r) (G.coeff 2 : ZMod r)
        (G.coeff 1 : ZMod r) ((y.val : Nat) : ZMod r) := by
      simp [fifthPolynomialFormal, fifthPolynomial]

/-- Cancelling a common integer factor from both a phase and its modulus
preserves the standard additive character. -/
theorem stdAddChar_intCast_mul_modulus (r d : Nat) [NeZero r] [NeZero d]
    (z : Int) :
    ZMod.stdAddChar (((d : Int) * z : Int) : ZMod (r * d)) =
      ZMod.stdAddChar (z : ZMod r) := by
  calc
    ZMod.stdAddChar (((d : Int) * z : Int) : ZMod (r * d)) =
        ZMod.stdAddChar (zmodScale r d (z : ZMod r)) := by
      apply congrArg ZMod.stdAddChar
      rw [zmodScale_intCast]
      push_cast
      ring
    _ = ZMod.stdAddChar (z : ZMod r) := stdAddChar_zmodScale r d _

/-- A polynomial phase modulo `r` is periodic with period `r` on integer
representatives. -/
theorem stdAddChar_polynomial_eval_finProdFinEquiv (u r : Nat) [NeZero r]
    (F : Polynomial Int) (i : Fin u) (y : Fin r) :
    ZMod.stdAddChar
        ((F.eval ((finProdFinEquiv (i, y)).val : Int) : Int) : ZMod r) =
      ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) := by
  apply congrArg ZMod.stdAddChar
  change (Int.castRingHom (ZMod r))
      (F.eval ((finProdFinEquiv (i, y)).val : Int)) =
    (Int.castRingHom (ZMod r)) (F.eval (y.val : Int))
  rw [← Polynomial.eval_map_apply, ← Polynomial.eval_map_apply]
  congr 1
  change (((y.val + r * i.val : Nat) : Int) : ZMod r) =
    ((y.val : Int) : ZMod r)
  push_cast
  rw [ZMod.natCast_self]
  simp

/-- Summing a polynomial phase over `u` complete periods gives `u` times one
complete sum. -/
theorem sum_polynomial_phase_repeated (u r : Nat) [NeZero r]
    (F : Polynomial Int) :
    (∑ k : Fin (u * r),
        ZMod.stdAddChar ((F.eval (k.val : Int) : Int) : ZMod r)) =
      (u : Complex) *
        ∑ y : Fin r,
          ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) := by
  rw [← (finProdFinEquiv : Fin u × Fin r ≃ Fin (u * r)).sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : Fin u, ∑ y : Fin r,
        ZMod.stdAddChar
          ((F.eval ((finProdFinEquiv (i, y)).val : Int) : Int) : ZMod r)) =
        ∑ _i : Fin u, ∑ y : Fin r,
          ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro y _
      exact stdAddChar_polynomial_eval_finProdFinEquiv u r F i y
    _ = (u : Complex) * ∑ y : Fin r,
        ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) := by simp

/-- Combining common-factor cancellation with finite-period reindexing gives
the exact quotient/repetition identity used in a critical block. -/
theorem sum_scaled_polynomial_phase_repeated (u r d : Nat)
    [NeZero r] [NeZero d] (F : Polynomial Int) :
    (∑ k : Fin (u * r),
        ZMod.stdAddChar
          ((((d : Int) * F.eval (k.val : Int) : Int)) : ZMod (r * d))) =
      (u : Complex) *
        ∑ y : Fin r,
          ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) := by
  calc
    (∑ k : Fin (u * r),
        ZMod.stdAddChar
          ((((d : Int) * F.eval (k.val : Int) : Int)) : ZMod (r * d))) =
        ∑ k : Fin (u * r),
          ZMod.stdAddChar ((F.eval (k.val : Int) : Int) : ZMod r) := by
      apply Finset.sum_congr rfl
      intro k _
      exact stdAddChar_intCast_mul_modulus r d _
    _ = (u : Complex) *
        ∑ y : Fin r,
          ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod r) :=
      sum_polynomial_phase_repeated u r F

/-- A critical block whose length is `u*r` and whose modulus is
`r*p^sigma` is exactly `u` copies of the complete quotient sum modulo `r`. -/
theorem fifthCriticalBlockSum_eq_repeated_quotient
    (p u r : Nat) [Fact p.Prime] [NeZero p] [NeZero r]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) :
    fifthCriticalBlockSum
        (q := r * p ^ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄)
        p (u * r) x a₀ a₁ a₂ a₃ a₄ =
      (u : Complex) *
        integerPolynomialCompleteSum (q := r)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 5)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 4)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 3)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 2)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 1) := by
  let sigma := fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄
  let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
  have hfactor := fifthCriticalTranslate_eq_C_pow_mul_fifthCriticalQuotient
    p x a₀ a₁ a₂ a₃ a₄
  rw [fifthCriticalBlockSum]
  calc
    (∑ k : Fin (u * r),
        ZMod.stdAddChar
          (((fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) : Int) : ZMod (r * p ^ sigma))) =
        ∑ k : Fin (u * r),
          ZMod.stdAddChar
            ((((p : Int) ^ sigma * G.eval (k.val : Int) : Int)) :
              ZMod (r * p ^ sigma)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply congrArg ZMod.stdAddChar
      apply congrArg (fun z : Int ↦ (z : ZMod (r * p ^ sigma)))
      have heval := congrArg
        (fun F : Polynomial Int ↦ F.eval (k.val : Int)) hfactor
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using heval
    _ = (u : Complex) * ∑ y : Fin r,
        ZMod.stdAddChar ((G.eval (y.val : Int) : Int) : ZMod r) := by
      exact sum_scaled_polynomial_phase_repeated u r (p ^ sigma) G
    _ = (u : Complex) *
        integerPolynomialCompleteSum (q := r)
          (G.coeff 5) (G.coeff 4) (G.coeff 3)
          (G.coeff 2) (G.coeff 1) := by
      rw [sum_fifthCriticalQuotient_eq_integerPolynomialCompleteSum
        (p := p) x a₀ a₁ a₂ a₃ a₄]

end Waring.Analytic
