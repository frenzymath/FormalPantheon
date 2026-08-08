import Waring.Analytic.ChenFourTranslation

/-!
# Critical block sums in Chen's Lemma 4

This file connects the residue-root decomposition to Chen's translated integer
polynomial, retaining the exact constant character on each critical block
[CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Complete polynomial sum with integer coefficients cast into the residue
ring of the modulus. -/
noncomputable def integerPolynomialCompleteSum {q : Nat} [NeZero q]
    (a₀ a₁ a₂ a₃ a₄ : Int) : Complex :=
  polynomialCompleteSum
    (a₀ : ZMod q) (a₁ : ZMod q) (a₂ : ZMod q)
    (a₃ : ZMod q) (a₄ : ZMod q)

/-- The translated phase sum over the high coordinates of one derivative-root
block. -/
noncomputable def fifthCriticalBlockSum {q : Nat} [NeZero q]
    (p s : Nat) (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int) : Complex :=
  ∑ k : Fin s, ZMod.stdAddChar
    (((fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
      (k.val : Int) : Int) : ZMod q)

/-- Canonical reduction of an integer cast agrees across a divisor of the
modulus. -/
theorem zmodPrimeReduction_intCast (p m : Nat) (a : Int) :
    zmodPrimeReduction p m (a : ZMod (p * m)) = (a : ZMod p) := by
  simp [zmodPrimeReduction]

/-- The source representative attached to `(x,k)` is `x.val+p*k.val`. -/
@[simp] theorem derivativeRootBlockIndex_val (p s : Nat)
    [NeZero p] [NeZero s] (x : ZMod p) (k : Fin s) :
    (derivativeRootBlockIndex p s x k).val = x.val + p * k.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => rfl

/-- On a derivative-root block, the original integer phase is the value at the
root plus the translated critical polynomial. -/
theorem fifthPolynomial_derivativeRootBlockIndex_eq_add_translate
    (p s : Nat) [NeZero p] [NeZero s] (x : ZMod p) (k : Fin s)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    fifthPolynomial
        (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
        (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
        (a₄ : ZMod (p * (p * s)))
        (((derivativeRootBlockIndex p s x k).val : Nat) :
          ZMod (p * (p * s))) =
      fifthPolynomial
          (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
          (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
          (a₄ : ZMod (p * (p * s)))
          ((x.val : Nat) : ZMod (p * (p * s))) +
        (((fifthCriticalTranslate p (x.val : Int) a₀ a₁ a₂ a₃ a₄).eval
          (k.val : Int) : Int) : ZMod (p * (p * s))) := by
  have hint :
      fifthPolynomial a₀ a₁ a₂ a₃ a₄
          ((x.val : Int) + p * (k.val : Int)) =
        fifthPolynomial a₀ a₁ a₂ a₃ a₄ (x.val : Int) +
          (fifthCriticalTranslate p (x.val : Int) a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) := by
    rw [eval_fifthCriticalTranslate]
    ring
  rw [derivativeRootBlockIndex_val]
  have hcast := congrArg
    (fun z : Int ↦ (z : ZMod (p * (p * s)))) hint
  simp [fifthPolynomial] at hcast ⊢

/-- Additivity of the standard character gives the source's phase
factorization on a critical block. -/
theorem stdAddChar_fifthPolynomial_derivativeRootBlockIndex (p s : Nat)
    [NeZero p] [NeZero s] (x : ZMod p) (k : Fin s)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    ZMod.stdAddChar
        (fifthPolynomial
          (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
          (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
          (a₄ : ZMod (p * (p * s)))
          (((derivativeRootBlockIndex p s x k).val : Nat) :
            ZMod (p * (p * s)))) =
      ZMod.stdAddChar
          (fifthPolynomial
            (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
            (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
            (a₄ : ZMod (p * (p * s)))
            ((x.val : Nat) : ZMod (p * (p * s)))) *
        ZMod.stdAddChar
          (((fifthCriticalTranslate p (x.val : Int) a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) : Int) : ZMod (p * (p * s))) := by
  rw [fifthPolynomial_derivativeRootBlockIndex_eq_add_translate]
  exact ZMod.stdAddChar.map_add_eq_mul _ _

/-- Each critical block factors into its constant root character and the
translated polynomial block sum. -/
theorem sum_derivativeRootBlock_eq_mul_fifthCriticalBlockSum (p s : Nat)
    [NeZero p] [NeZero s] (x : ZMod p)
    (a₀ a₁ a₂ a₃ a₄ : Int) :
    (∑ k : Fin s, (p : Complex) * ZMod.stdAddChar
      (fifthPolynomial
        (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
        (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
        (a₄ : ZMod (p * (p * s)))
        (((derivativeRootBlockIndex p s x k).val : Nat) :
          ZMod (p * (p * s))))) =
      ((p : Complex) * ZMod.stdAddChar
        (fifthPolynomial
          (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
          (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
          (a₄ : ZMod (p * (p * s)))
          ((x.val : Nat) : ZMod (p * (p * s))))) *
        fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
          a₀ a₁ a₂ a₃ a₄ := by
  rw [fifthCriticalBlockSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [stdAddChar_fifthPolynomial_derivativeRootBlockIndex]
  ring

/-- Chen's exact critical-block decomposition for integer coefficients. -/
theorem integerPolynomialCompleteSum_eq_sum_criticalBlocks (p s : Nat)
    [Fact p.Prime] [NeZero p] [NeZero s] (hp : 11 ≤ p)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    integerPolynomialCompleteSum (q := p * (p * s)) a₀ a₁ a₂ a₃ a₄ =
      ∑ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        ((p : Complex) * ZMod.stdAddChar
          (fifthPolynomial
            (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
            (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
            (a₄ : ZMod (p * (p * s)))
            ((x.val : Nat) : ZMod (p * (p * s))))) *
          fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄ := by
  rw [integerPolynomialCompleteSum]
  rw [polynomialCompleteSum_eq_sum_derivativeRootBlocks p s
    (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
    (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
    (a₄ : ZMod (p * (p * s))) hp (by simpa using hcoeff)]
  simp only [zmodPrimeReduction_intCast]
  apply Finset.sum_congr rfl
  intro x _
  exact sum_derivativeRootBlock_eq_mul_fifthCriticalBlockSum
    p s x a₀ a₁ a₂ a₃ a₄

/-- Taking norms in the critical-block decomposition leaves `p` times the sum
of translated block norms. -/
theorem norm_integerPolynomialCompleteSum_le_sum_criticalBlockNorms
    (p s : Nat) [Fact p.Prime] [NeZero p] [NeZero s] (hp : 11 ≤ p)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    ‖integerPolynomialCompleteSum (q := p * (p * s))
        a₀ a₁ a₂ a₃ a₄‖ ≤
      (p : Real) *
        ∑ x ∈ fifthDerivativeRoots
            (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
            (a₃ : ZMod p) (a₄ : ZMod p),
          ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄‖ := by
  rw [integerPolynomialCompleteSum_eq_sum_criticalBlocks p s hp
    a₀ a₁ a₂ a₃ a₄ hcoeff]
  calc
    ‖∑ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        ((p : Complex) * ZMod.stdAddChar
          (fifthPolynomial
            (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
            (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
            (a₄ : ZMod (p * (p * s)))
            ((x.val : Nat) : ZMod (p * (p * s))))) *
          fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄‖ ≤
        ∑ x ∈ fifthDerivativeRoots
            (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
            (a₃ : ZMod p) (a₄ : ZMod p),
          ‖((p : Complex) * ZMod.stdAddChar
            (fifthPolynomial
              (a₀ : ZMod (p * (p * s))) (a₁ : ZMod (p * (p * s)))
              (a₂ : ZMod (p * (p * s))) (a₃ : ZMod (p * (p * s)))
              (a₄ : ZMod (p * (p * s)))
              ((x.val : Nat) : ZMod (p * (p * s))))) *
            fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
              a₀ a₁ a₂ a₃ a₄‖ := norm_sum_le _ _
    _ = (p : Real) *
        ∑ x ∈ fifthDerivativeRoots
            (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
            (a₃ : ZMod p) (a₄ : ZMod p),
          ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp

end Waring.Analytic
