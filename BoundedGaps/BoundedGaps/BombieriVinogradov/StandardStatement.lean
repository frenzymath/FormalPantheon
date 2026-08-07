import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Chebyshev

/-!
# Standard weighted Bombieri--Vinogradov statement

This Mathlib-only file states the natural-endpoint specialization of the
weighted progression estimate in `Vaughan1980`, pp. 113--115, equation (9).
The final declaration is a proposition only; this file asserts no theorem
proving Bombieri--Vinogradov.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace BoundedGaps.BombieriVinogradov

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

end BoundedGaps.BombieriVinogradov
