import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting

/-!
# Standalone Bombieri--Vinogradov challenge

Mathlib-only specification of the natural-endpoint and standard weighted
interfaces. The placeholders are authorized only in this isolated Challenge
module by PUB-SEM-030 and PUB-SEM-031. This module must never enter a
production proof closure.

Primary source: `Maynard2013v3`, equation (1.3), TeX lines 56--60; interval
error equation (5.16), printed page 11. The standard weighted extension is
the natural-endpoint specialization of `Vaughan1980`, pp. 113--115,
especially equation (9).
-/

namespace BoundedGaps.BombieriVinogradov.Comparator

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- Reduced residue representatives in the range `0 <= a < q`. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (Nat.Coprime · q)

theorem coprimeResidues_nonempty {q : ℕ} (hq : 0 < q) :
    (coprimeResidues q).Nonempty := by
  sorry

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

/-- Bombieri--Vinogradov supplies every fixed positive prime level strictly
below one half. -/
theorem unconditional_bombieriVinogradov : bombieriVinogradov := by
  sorry

/-- Reduced residue representatives in the range `0 <= a < q`. -/
def reducedResidues (q : Nat) : Finset Nat :=
  (Finset.range q).filter (Nat.Coprime · q)

theorem reducedResidues_nonempty {q : Nat} (hq : 0 < q) :
    (reducedResidues q).Nonempty := by
  by_cases hq1 : q = 1
  · subst q
    simp [reducedResidues]
  · have hq0 : q ≠ 0 := Nat.ne_of_gt hq
    have h1q : 1 < q :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hq0, hq1⟩
    refine ⟨1, ?_⟩
    simp [reducedResidues, h1q]

theorem endpointRange_nonempty {x : Nat} (hx : 2 <= x) :
    (Finset.Icc 2 x).Nonempty :=
  ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩

/-- The von Mangoldt sum over positive `n <= x` in the class `a (mod q)`. -/
noncomputable def chebyshevProgressionSum (x q a : Nat) : Real :=
  ∑ n ∈ Finset.Icc 1 x with n % q = a % q,
    ArithmeticFunction.vonMangoldt n

/-- Weighted progression discrepancy centered at the source term `x / phi(q)`. -/
noncomputable def weightedProgressionDiscrepancy
    (x q a : Nat) : Real :=
  |chebyshevProgressionSum x q a -
    (x : Real) / (Nat.totient q : Real)|

/-- The source-ordered maximum over reduced residues and natural endpoints. -/
noncomputable def maxWeightedProgressionDiscrepancyUpTo
    (x q : Nat) : Real :=
  if hx : 2 <= x then
    if hq : 0 < q then
      (reducedResidues q).sup' (reducedResidues_nonempty hq) (fun a =>
        (Finset.Icc 2 x).sup' (endpointRange_nonempty hx) (fun y =>
          weightedProgressionDiscrepancy y q a))
    else 0
  else 0

/-- Vaughan's natural-endpoint logarithmic-window weighted contract. -/
def weightedBombieriVinogradov : Prop :=
  ∀ A : Real, 0 < A →
    ∃ B : Nat, A + 4 < (B : Real) ∧
    ∃ C : Real, 0 <= C ∧
    ∃ X0 : Nat, 4 <= X0 ∧
      ∀ x : Nat, X0 <= x →
      ∀ Q : Nat, 1 <= Q →
        (Q : Real) <= Real.sqrt (x : Real) /
          (Real.log (x : Real)) ^ B →
        (∑ q ∈ Finset.Icc 1 Q,
          maxWeightedProgressionDiscrepancyUpTo x q) <=
          C * (x : Real) /
            Real.rpow (Real.log (x : Real)) A

/-- The unconditional standard weighted Bombieri--Vinogradov theorem. -/
theorem unconditional_weightedBombieriVinogradov :
    weightedBombieriVinogradov := by
  sorry

end BoundedGaps.BombieriVinogradov.Comparator
