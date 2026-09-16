import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Independent challenge: primes with restricted decimal digits

James Maynard, *Primes with restricted digits*, Invent. Math. 217 (2019), 127--218, Theorem
1.1, pp.128--129. DOI: 10.1007/s00222-019-00865-6. Source key: `MAYNARD-PRD-PUBLISHED`.

This Mathlib-only interface fixes both quantitative comparisons and infinitude. Only the two
final theorem bodies are expected solver obligations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits.Comparator

/-- Standard decimal digits, with zero represented by `[0]`. Digit order is little-endian. -/
def standardDecimalDigits (n : ℕ) : List ℕ :=
  if n = 0 then [0] else Nat.digits 10 n

/-- No digit in the standard decimal representation equals the excluded digit. -/
def omitsDecimalDigit (a : Fin 10) (n : ℕ) : Prop :=
  ∀ d ∈ standardDecimalDigits n, d ≠ a.val

/-- Natural numbers strictly below a real cutoff whose decimal expansion omits a digit. -/
noncomputable def restrictedNumbers (a : Fin 10) (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.ceil X)).filter fun n =>
    (n : ℝ) < X ∧ omitsDecimalDigit a n

/-- Number of restricted natural numbers strictly below the cutoff. -/
noncomputable def restrictedCount (a : Fin 10) (X : ℝ) : ℕ :=
  (restrictedNumbers a X).card

/-- Number of restricted primes strictly below the cutoff. -/
noncomputable def restrictedPrimeCount (a : Fin 10) (X : ℝ) : ℕ := by
  classical
  exact (restrictedNumbers a X).filter Nat.Prime |>.card

/-- Both quantitative comparison links, with four absolute positive constants. -/
def quantitativeTheorem : Prop :=
  ∃ c₁ c₂ c₃ c₄ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
      ∀ (a : Fin 10) (X : ℝ), 4 ≤ X →
        c₁ * ((restrictedCount a X : ℝ) / Real.log X) <
            (restrictedPrimeCount a X : ℝ) ∧
          (restrictedPrimeCount a X : ℝ) <
            c₂ * ((restrictedCount a X : ℝ) / Real.log X) ∧
          c₃ * (X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) / Real.log X) <
            (restrictedCount a X : ℝ) / Real.log X ∧
          (restrictedCount a X : ℝ) / Real.log X <
            c₄ * (X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) / Real.log X)

/-- Infinitely many natural primes omit the specified decimal digit. -/
def infinitelyManyRestrictedPrimes (a : Fin 10) : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ omitsDecimalDigit a p}

/-- Infinitude for every excluded decimal digit. -/
def infinitudeCorollary : Prop :=
  ∀ a : Fin 10, infinitelyManyRestrictedPrimes a

set_option warn.sorry false in
/-- Maynard's full quantitative theorem, uniform in the digit and real cutoff. -/
theorem mainTheorem : quantitativeTheorem := by
  sorry

set_option warn.sorry false in
/-- The infinitude corollary for every excluded decimal digit. -/
theorem infinitude : infinitudeCorollary := by
  sorry

end PrimesRestrictedDigits.Comparator
