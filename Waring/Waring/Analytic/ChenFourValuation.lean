import Waring.Analytic.ChenFourTranslation
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

/-!
# Critical-block content valuations in Chen's Lemma 4

This file proves the coefficient valuation estimate used in the critical-block
induction of [CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].  If a residue is a
root of multiplicity `m` of the reduced derivative, the translated quintic has
content valuation between `2` and `m + 1`.
-/

namespace Waring.Analytic

/-- Hasse derivatives commute with maps of coefficient semirings. -/
theorem map_hasseDeriv {R S : Type*} [Semiring R] [Semiring S]
    (phi : R →+* S) (k : Nat) (f : Polynomial R) :
    (Polynomial.hasseDeriv k f).map phi =
      Polynomial.hasseDeriv k (f.map phi) := by
  ext n
  simp [Polynomial.hasseDeriv_coeff]

/-- A nonzero polynomial over a field has root multiplicity at most its
natural degree. -/
theorem rootMultiplicity_le_natDegree {K : Type*} [Field K]
    (f : Polynomial K) (x : K) (hf : f ≠ 0) :
    f.rootMultiplicity x ≤ f.natDegree := by
  have hdiv := f.pow_rootMultiplicity_dvd x
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv hf
  simpa using hdegree

/-- At a root of multiplicity `m` of `f'`, the Hasse derivative of `f` of
order `m+1` does not vanish. -/
theorem eval_hasseDeriv_succ_rootMultiplicity_ne_zero
    {K : Type*} [Field K] (f : Polynomial K) (x : K)
    (hderivative : f.derivative ≠ 0) :
    (Polynomial.hasseDeriv (f.derivative.rootMultiplicity x + 1) f).eval x ≠ 0 := by
  let derivative := f.derivative
  let m := derivative.rootMultiplicity x
  have htaylor_ne : derivative.taylor x ≠ 0 := by
    apply (Polynomial.taylor_eq_zero x derivative).not.mpr
    simpa only [derivative] using hderivative
  have hm : m = (derivative.taylor x).natTrailingDegree := by
    simpa only [m, Polynomial.taylor_apply] using
      (Polynomial.rootMultiplicity_eq_natTrailingDegree
        (p := derivative) (t := x))
  have hcoeff : (derivative.taylor x).coeff m ≠ 0 := by
    rw [hm]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr htaylor_ne
  have hderivative_taylor :
      (f.taylor x).derivative = derivative.taylor x := by
    simp [derivative, Polynomial.taylor_apply, Polynomial.derivative_comp]
  have hrelation :
      (derivative.taylor x).coeff m =
        (f.taylor x).coeff (m + 1) * (m + 1 : Nat) := by
    rw [← hderivative_taylor, Polynomial.coeff_derivative]
    push_cast
    rfl
  have htaylorCoeff : (f.taylor x).coeff (m + 1) ≠ 0 := by
    intro hzero
    apply hcoeff
    rw [hrelation, hzero, zero_mul]
  simpa only [m, derivative, Polynomial.taylor_coeff] using htaylorCoeff

/-- The multiplicity of a critical residue of Chen's reduced quintic
derivative is at most four. -/
theorem fifthDerivativeMultiplicity_le_four {p : Nat} [Fact p.Prime]
    (a₀ a₁ a₂ a₃ a₄ x : ZMod p)
    (hderivative : fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄ ≠ 0) :
    fifthDerivativeMultiplicity a₀ a₁ a₂ a₃ a₄ x ≤ 4 := by
  exact (rootMultiplicity_le_natDegree
      (fifthPolynomialDerivative a₀ a₁ a₂ a₃ a₄) x hderivative).trans
    (natDegree_fifthPolynomialDerivative_le a₀ a₁ a₂ a₃ a₄)

/-- The first Hasse derivative after a critical root's multiplicity is
nonzero modulo `p`. -/
theorem eval_hasseDeriv_fifthPolynomial_succ_rootMultiplicity_ne_zero
    {p : Nat} [Fact p.Prime] (hp : 11 ≤ p)
    (a₀ a₁ a₂ a₃ a₄ x : ZMod p)
    (hcoeff :
      a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ a₂ ≠ 0 ∨ a₃ ≠ 0 ∨ a₄ ≠ 0) :
    let f := fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄
    let m := f.derivative.rootMultiplicity x
    (Polynomial.hasseDeriv (m + 1)
        (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)).eval x ≠ 0 := by
  dsimp only
  let f := fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄
  have hderivative : f.derivative ≠ 0 := by
    rw [derivative_fifthPolynomialFormal]
    exact fifthPolynomialDerivative_ne_zero Fact.out hp _ _ _ _ _ hcoeff
  exact eval_hasseDeriv_succ_rootMultiplicity_ne_zero f x hderivative

/-- The coefficient of degree `m+1` in a critical translate is not divisible
by `p^(m+2)`, where `m` is the derivative-root multiplicity. -/
theorem prime_pow_succ_multiplicity_not_dvd_coeff_fifthCriticalTranslate
    {p : Nat} [Fact p.Prime] (hp : 11 ≤ p) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨ (a₂ : ZMod p) ≠ 0 ∨
        (a₃ : ZMod p) ≠ 0 ∨ (a₄ : ZMod p) ≠ 0) :
    let m := fifthDerivativeMultiplicity
      (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
        (a₄ : ZMod p) (x : ZMod p)
    ¬(p : Int) ^ (m + 2) ∣
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).coeff (m + 1) := by
  dsimp only
  let m := fifthDerivativeMultiplicity
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
      (a₄ : ZMod p) (x : ZMod p)
  rw [coeff_succ_fifthCriticalTranslate]
  intro hdiv
  have hpPrime : p.Prime := Fact.out
  have hpne : (p : Int) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hcancel : (p : Int) ∣
      (Polynomial.hasseDeriv (m + 1)
        (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)).eval x := by
    rw [pow_succ'] at hdiv
    exact (Int.mul_dvd_mul_iff_right (pow_ne_zero (m + 1) hpne)).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hcancel
  have hcastEval :
      (Polynomial.hasseDeriv (m + 1)
        (fifthPolynomialFormal
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
            (a₃ : ZMod p) (a₄ : ZMod p))).eval (x : ZMod p) = 0 := by
    simpa [← Polynomial.eval_map_apply, map_hasseDeriv,
      fifthPolynomialFormal] using hcancel
  have hm :
      (fifthPolynomialFormal
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
            (a₃ : ZMod p) (a₄ : ZMod p)).derivative.rootMultiplicity
          (x : ZMod p) = m := by
    rw [derivative_fifthPolynomialFormal]
    rfl
  have hnonzero := eval_hasseDeriv_fifthPolynomial_succ_rootMultiplicity_ne_zero hp
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
      (a₄ : ZMod p) (x : ZMod p) hcoeff
  dsimp only at hnonzero
  rw [hm] at hnonzero
  exact hnonzero hcastEval

/-- At a critical residue, the common content valuation of Chen's translated
quintic is at least two. -/
theorem two_le_padicValInt_content_fifthCriticalTranslate
    {p : Nat} [Fact p.Prime] (hp : 11 ≤ p) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨ (a₂ : ZMod p) ≠ 0 ∨
        (a₃ : ZMod p) ≠ 0 ∨ (a₄ : ZMod p) ≠ 0)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    2 ≤ padicValInt p
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content := by
  have hdiv := prime_sq_dvd_content_fifthCriticalTranslate
    p x a₀ a₁ a₂ a₃ a₄ hroot
  rw [padicValInt_dvd_iff] at hdiv
  rcases hdiv with hzero | hbound
  · have htranslate :
        fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ ≠ 0 := by
      intro htranslate
      have hcoeffzero := congrArg
        (fun f : Polynomial Int ↦ f.coeff
          (fifthDerivativeMultiplicity
            (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
              (a₄ : ZMod p) (x : ZMod p) + 1)) htranslate
      apply prime_pow_succ_multiplicity_not_dvd_coeff_fifthCriticalTranslate
        hp x a₀ a₁ a₂ a₃ a₄ hcoeff
      simp [hcoeffzero]
    have hcontentne :
        (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content ≠ 0 :=
      Polynomial.content_eq_zero_iff.not.mpr htranslate
    exact (hcontentne hzero).elim
  · exact hbound

/-- At a critical residue of derivative multiplicity `m`, the common content
valuation of Chen's translated quintic is at most `m+1`. -/
theorem padicValInt_content_fifthCriticalTranslate_le_succ_multiplicity
    {p : Nat} [Fact p.Prime] (hp : 11 ≤ p) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨ (a₂ : ZMod p) ≠ 0 ∨
        (a₃ : ZMod p) ≠ 0 ∨ (a₄ : ZMod p) ≠ 0) :
    padicValInt p
        (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content ≤
      fifthDerivativeMultiplicity
        (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
          (a₄ : ZMod p) (x : ZMod p) + 1 := by
  let m := fifthDerivativeMultiplicity
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
      (a₄ : ZMod p) (x : ZMod p)
  by_contra! hlarge
  have hpowContent : (p : Int) ^ (m + 2) ∣
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content := by
    rw [padicValInt_dvd_iff]
    exact Or.inr hlarge
  have hpowCoeff : (p : Int) ^ (m + 2) ∣
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).coeff (m + 1) :=
    hpowContent.trans (Polynomial.content_dvd_coeff (m + 1))
  exact prime_pow_succ_multiplicity_not_dvd_coeff_fifthCriticalTranslate
    hp x a₀ a₁ a₂ a₃ a₄ hcoeff hpowCoeff

/-- Chen's complete content-valuation interval at a critical derivative root:
`2 ≤ sigma ≤ m + 1`. -/
theorem padicValInt_content_fifthCriticalTranslate_mem_interval
    {p : Nat} [Fact p.Prime] (hp : 11 ≤ p) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨ (a₂ : ZMod p) ≠ 0 ∨
        (a₃ : ZMod p) ≠ 0 ∨ (a₄ : ZMod p) ≠ 0)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    2 ≤ padicValInt p
        (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content ∧
      padicValInt p
          (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content ≤
        fifthDerivativeMultiplicity
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p) (a₃ : ZMod p)
            (a₄ : ZMod p) (x : ZMod p) + 1 := by
  exact ⟨two_le_padicValInt_content_fifthCriticalTranslate
      hp x a₀ a₁ a₂ a₃ a₄ hcoeff hroot,
    padicValInt_content_fifthCriticalTranslate_le_succ_multiplicity
      hp x a₀ a₁ a₂ a₃ a₄ hcoeff⟩

end Waring.Analytic
