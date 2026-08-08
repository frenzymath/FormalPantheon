import Waring.Analytic.ChenFourStationary

/-!
# Critical-block translations in Chen's Lemma 4

This file records the exact Taylor polynomial behind the translated critical
blocks in [CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].
-/

namespace Waring.Analytic

/-- The polynomial `f(center + scale*X) - f(center)`, expressed through
Mathlib's Taylor polynomial. -/
noncomputable def scaledTaylorDifference {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) : Polynomial R :=
  (f.taylor center).comp (Polynomial.C scale * Polynomial.X) -
    Polynomial.C (f.eval center)

/-- Evaluation of the scaled Taylor difference has the intended translated
polynomial value. -/
@[simp] theorem eval_scaledTaylorDifference {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) (y : R) :
    (scaledTaylorDifference scale center f).eval y =
      f.eval (center + scale * y) - f.eval center := by
  simp [scaledTaylorDifference, Polynomial.taylor_eval, add_comm]

/-- The translated difference has zero constant coefficient. -/
@[simp] theorem coeff_zero_scaledTaylorDifference {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) :
    (scaledTaylorDifference scale center f).coeff 0 = 0 := by
  simp [scaledTaylorDifference, Polynomial.comp_C_mul_X_coeff,
    Polynomial.taylor_coeff_zero]

/-- Every positive coefficient is the corresponding Hasse derivative,
multiplied by the appropriate power of the scale. -/
theorem coeff_succ_scaledTaylorDifference {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) (n : Nat) :
    (scaledTaylorDifference scale center f).coeff (n + 1) =
      (Polynomial.hasseDeriv (n + 1) f).eval center * scale ^ (n + 1) := by
  simp [scaledTaylorDifference, Polynomial.comp_C_mul_X_coeff,
    Polynomial.taylor_coeff]

/-- The linear coefficient is the scale times the ordinary derivative at the
center. -/
theorem coeff_one_scaledTaylorDifference {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) :
    (scaledTaylorDifference scale center f).coeff 1 =
      f.derivative.eval center * scale := by
  simpa [Polynomial.hasseDeriv_one'] using
    coeff_succ_scaledTaylorDifference scale center f 0

/-- Scaled Taylor differences commute with coefficient ring homomorphisms. -/
theorem map_scaledTaylorDifference {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (scale center : R) (f : Polynomial R) :
    (scaledTaylorDifference scale center f).map phi =
      scaledTaylorDifference (phi scale) (phi center) (f.map phi) := by
  simp [scaledTaylorDifference, Polynomial.map_comp]

/-- Scaling and translating a polynomial does not increase a known natural
degree bound. -/
theorem natDegree_scaledTaylorDifference_le {R : Type*} [CommRing R]
    (scale center : R) (f : Polynomial R) (n : Nat)
    (hf : f.natDegree ≤ n) :
    (scaledTaylorDifference scale center f).natDegree ≤ n := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_comp_le.trans
    rw [Polynomial.natDegree_taylor]
    have hinner :
        (Polynomial.C scale * Polynomial.X).natDegree ≤ 1 := by
      simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le scale 1)
    calc
      f.natDegree * (Polynomial.C scale * Polynomial.X).natDegree ≤
          f.natDegree * 1 := Nat.mul_le_mul_left _ hinner
      _ = f.natDegree := Nat.mul_one _
      _ ≤ n := hf
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le n

/-- Chen's formal polynomial has degree at most five, including when leading
coefficients vanish. -/
theorem natDegree_fifthPolynomialFormal_le_five
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).natDegree ≤ 5 := by
  have hterm (a : Int) (n : Nat) (hn : n ≤ 5) :
      (Polynomial.monomial n a).natDegree ≤ 5 :=
    (Polynomial.natDegree_monomial_le a).trans hn
  unfold fifthPolynomialFormal
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact hterm _ 5 le_rfl
        · exact hterm _ 4 (by omega)
      · exact hterm _ 3 (by omega)
    · exact hterm _ 2 (by omega)
  · exact hterm _ 1 (by omega)

/-- Chen's translated integer quintic `f(x+p*X)-f(x)`. -/
noncomputable def fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) : Polynomial Int :=
  scaledTaylorDifference (p : Int) x
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)

/-- Chen's translated critical polynomial still has degree at most five. -/
theorem natDegree_fifthCriticalTranslate_le_five (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).natDegree ≤ 5 := by
  exact natDegree_scaledTaylorDifference_le _ _ _ 5
    (natDegree_fifthPolynomialFormal_le_five a₀ a₁ a₂ a₃ a₄)

/-- Evaluation of Chen's translated quintic. -/
@[simp] theorem eval_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ y : Int) :
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval y =
      fifthPolynomial a₀ a₁ a₂ a₃ a₄ (x + p * y) -
        fifthPolynomial a₀ a₁ a₂ a₃ a₄ x := by
  simp [fifthCriticalTranslate]

/-- Positive coefficients of the translated quintic have the source's exact
Taylor/Hasse-derivative form. -/
theorem coeff_succ_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) (n : Nat) :
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).coeff (n + 1) =
      (Polynomial.hasseDeriv (n + 1)
          (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)).eval x *
        (p : Int) ^ (n + 1) := by
  exact coeff_succ_scaledTaylorDifference _ _ _ _

/-- The translated quintic has zero constant coefficient. -/
@[simp] theorem coeff_zero_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).coeff 0 = 0 := by
  exact coeff_zero_scaledTaylorDifference _ _ _

/-- A derivative root modulo `p` says that `p` divides the corresponding
integer derivative value. -/
theorem prime_dvd_eval_fifthPolynomialDerivative_of_modEq_zero (p : Nat)
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    (p : Int) ∣
      (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄).derivative.eval x := by
  rw [derivative_fifthPolynomialFormal]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa [eval_fifthPolynomialDerivative] using hroot

/-- At a derivative root modulo `p`, every coefficient of the translated
quintic is divisible by `p^2`. -/
theorem prime_sq_dvd_coeff_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0)
    (n : Nat) :
    (p : Int) ^ 2 ∣
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).coeff n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_succ_fifthCriticalTranslate]
      cases n with
      | zero =>
          have hdiv := prime_dvd_eval_fifthPolynomialDerivative_of_modEq_zero
            p x a₀ a₁ a₂ a₃ a₄ hroot
          simpa [Polynomial.hasseDeriv_one', pow_two] using
            mul_dvd_mul hdiv (dvd_refl (p : Int))
      | succ n =>
          apply dvd_mul_of_dvd_right
          exact pow_dvd_pow (p : Int) (by omega)

/-- Polynomial form of the common `p^2` divisibility in a critical block. -/
theorem C_prime_sq_dvd_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    Polynomial.C ((p : Int) ^ 2) ∣
      fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  exact prime_sq_dvd_coeff_fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ hroot

/-- The content of a critical translated quintic is divisible by `p^2`. -/
theorem prime_sq_dvd_content_fifthCriticalTranslate (p : Nat) (x : Int)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hroot :
      (fifthPolynomialDerivative
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p)).eval (x : ZMod p) = 0) :
    (p : Int) ^ 2 ∣
      (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).content := by
  exact Polynomial.dvd_content_iff_C_dvd.mpr
    (C_prime_sq_dvd_fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄ hroot)

end Waring.Analytic
