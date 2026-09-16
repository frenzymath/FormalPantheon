import Waring.Analytic.ChenFourPrimePowerInduction

/-!
# Prime-field reduction in Chen's Lemma 4

This file isolates the numerical endpoint of the still-open prime-field
estimate in Chen's Lemma 4.  The triangle inequality supplies the modulus
bound, so a uniform `5 * sqrt p` estimate implies Chen's exact max/min
constant [CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The triangle inequality bounds every complete polynomial sum by the
number of residues in the modulus. -/
theorem norm_integerPolynomialCompleteSum_le_modulus
    (q : Nat) [NeZero q] (a₀ a₁ a₂ a₃ a₄ : Int) :
    ‖integerPolynomialCompleteSum (q := q) a₀ a₁ a₂ a₃ a₄‖ ≤ q := by
  rw [integerPolynomialCompleteSum, polynomialCompleteSum]
  calc
    ‖∑ x : ZMod q,
        ZMod.stdAddChar
          (fifthPolynomial (a₀ : ZMod q) (a₁ : ZMod q) (a₂ : ZMod q)
            (a₃ : ZMod q) (a₄ : ZMod q) x)‖ ≤
        ∑ x : ZMod q,
          ‖ZMod.stdAddChar
            (fifthPolynomial (a₀ : ZMod q) (a₁ : ZMod q) (a₂ : ZMod q)
              (a₃ : ZMod q) (a₄ : ZMod q) x)‖ := norm_sum_le _ _
    _ = q := by simp

/-- The remaining Weil-type input at a prime: every primitive polynomial
phase has complete sum at most `5 * sqrt p`. -/
def ChenFourPrimeFieldSquareRootBound (p : Nat) [NeZero p] : Prop :=
  ∀ a₀ a₁ a₂ a₃ a₄ : Int,
    (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0 →
    ‖integerPolynomialCompleteSum (q := p) a₀ a₁ a₂ a₃ a₄‖ ≤
      5 * Real.sqrt p

/-- The minimum of the trivial and square-root estimates is bounded by
Chen's exact normalized prime factor. -/
theorem min_modulus_five_sqrt_le_chenFourPrimeFactor_mul
    (p : Nat) (hp : 0 < p) :
    min (p : Real) (5 * Real.sqrt p) ≤
      chenFourPrimeFactor p * (p : Real) ^ (4 / 5 : Real) := by
  have hpReal : (0 : Real) < p := by exact_mod_cast hp
  have hpow : 0 ≤ (p : Real) ^ (4 / 5 : Real) :=
    Real.rpow_nonneg (by positivity) _
  have hpSplit :
      (p : Real) =
        (p : Real) ^ (1 / 5 : Real) * (p : Real) ^ (4 / 5 : Real) := by
    rw [← Real.rpow_add hpReal]
    norm_num
  have hsqrtSplit :
      5 * Real.sqrt p =
        (5 * (p : Real) ^ (-(3 / 10) : Real)) *
          (p : Real) ^ (4 / 5 : Real) := by
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hpReal]
    norm_num
  calc
    min (p : Real) (5 * Real.sqrt p) = min
        ((p : Real) ^ (1 / 5 : Real) * (p : Real) ^ (4 / 5 : Real))
        ((5 * (p : Real) ^ (-(3 / 10) : Real)) *
          (p : Real) ^ (4 / 5 : Real)) := congrArg₂ min hpSplit hsqrtSplit
    _ =
      min ((p : Real) ^ (1 / 5 : Real))
          (5 * (p : Real) ^ (-(3 / 10) : Real)) *
        (p : Real) ^ (4 / 5 : Real) :=
      (min_mul_of_nonneg _ _ hpow).symm
    _ ≤ max 1
          (min ((p : Real) ^ (1 / 5 : Real))
            (5 * (p : Real) ^ (-(3 / 10) : Real))) *
        (p : Real) ^ (4 / 5 : Real) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpow
    _ = chenFourPrimeFactor p * (p : Real) ^ (4 / 5 : Real) := rfl

/-- The trivial modulus bound together with a `5 * sqrt p` estimate gives
Chen's exact primitive prime-field estimate. -/
theorem chenFourPrimeFieldBound_of_squareRootBound
    (p : Nat) [NeZero p] (hsqrt : ChenFourPrimeFieldSquareRootBound p) :
    ChenFourPrimeFieldBound p (chenFourPrimeFactor p) := by
  intro a₀ a₁ a₂ a₃ a₄ hcoeff
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  exact (le_min
    (norm_integerPolynomialCompleteSum_le_modulus p a₀ a₁ a₂ a₃ a₄)
    (hsqrt a₀ a₁ a₂ a₃ a₄ hcoeff)).trans
      (min_modulus_five_sqrt_le_chenFourPrimeFactor_mul p hp)

end Waring.Analytic
