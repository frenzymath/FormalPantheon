import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.PrimeCounting

/-!
# Bombieri--Vinogradov statement surface

This Mathlib-only file is the independent trust surface for Packet D. It
formalizes Maynard2013v3, equation `eq:LevelOfDistribution` (source lines
56--60), at natural endpoints. The final definition is a proposition only;
this file asserts no axiom or theorem proving Bombieri--Vinogradov.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Reduced residue representatives in the range `0 <= a < q`. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (Nat.Coprime · q)

theorem coprimeResidues_nonempty {q : ℕ} (hq : 0 < q) :
    (coprimeResidues q).Nonempty := by
  by_cases hq1 : q = 1
  · subst q
    simp [coprimeResidues]
  · have hq0 : q ≠ 0 := Nat.ne_of_gt hq
    have h1q : 1 < q :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hq0, hq1⟩
    refine ⟨1, ?_⟩
    simp [coprimeResidues, h1q]

/-- The number of primes `n <= x` in the residue class `a (mod q)`. -/
def primeCountUpTo (x q a : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter
    (fun n => n.Prime ∧ n % q = a % q)).card

/-- The total number of primes `n <= x`. -/
def primeCountTotal (x : ℕ) : ℕ :=
  Nat.primeCounting x

/-- Absolute discrepancy for one reduced residue representative. -/
noncomputable def progressionDiscrepancy (x q a : ℕ) : ℝ :=
  |(primeCountUpTo x q a : ℝ) -
    (primeCountTotal x : ℝ) / (Nat.totient q : ℝ)|

/-- The largest discrepancy among reduced residue representatives.

The zero-modulus branch is outside the theorem's positive-modulus sum. It
makes this definition total without hiding a nonzero hypothesis.
-/
noncomputable def maxProgressionDiscrepancy (x q : ℕ) : ℝ :=
  if hq : 0 < q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (progressionDiscrepancy x q)
  else 0

/-- The integral modulus cutoff `floor(x^theta)` for natural `x`. -/
noncomputable def modulusCutoff (θ : ℝ) (x : ℕ) : ℕ :=
  ⌊Real.rpow (x : ℝ) θ⌋₊

/-- Prime level of distribution `theta`, with all asymptotic uniformity
quantifiers explicit. Constants may depend on `A` and `theta`, but not on the
natural asymptotic variable `x`. -/
def hasPrimeLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
        (∑ q ∈ Finset.Icc 1 (modulusCutoff θ x),
          maxProgressionDiscrepancy x q) ≤
          C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A

/-- Bombieri--Vinogradov in the exact level language used by Maynard: every
fixed positive level below one half is available. -/
def bombieriVinogradov : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 / 2 → hasPrimeLevel θ

end BoundedGaps.Maynard
