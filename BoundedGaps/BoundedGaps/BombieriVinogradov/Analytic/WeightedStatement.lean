import BoundedGaps.BombieriVinogradov.Statement
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Chebyshev

/-!
# Weighted Bombieri--Vinogradov statement layer

This file records the natural-endpoint von Mangoldt interface selected in
`Vaughan1980` and cross-checked against `DavenportMNTCh28BV1980`. It defines
only finite sums, discrepancies, and a proposition contract. It proves no
Siegel--Walfisz, large-sieve, or Bombieri--Vinogradov theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The von Mangoldt sum over positive `n <= x` in the class `a (mod q)`. -/
noncomputable def chebyshevProgressionSum (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x with n % q = a % q,
    ArithmeticFunction.vonMangoldt n

/-- Weighted progression discrepancy centered at the source term `x / phi(q)`. -/
noncomputable def weightedProgressionDiscrepancy (x q a : ℕ) : ℝ :=
  |chebyshevProgressionSum x q a -
    (x : ℝ) / (Nat.totient q : ℝ)|

/-- Maximum weighted discrepancy over canonical reduced residue representatives. -/
noncomputable def maxWeightedProgressionDiscrepancy (x q : ℕ) : ℝ :=
  if hq : 0 < q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (weightedProgressionDiscrepancy x q)
  else 0

theorem weightedEndpointRange_nonempty {x : ℕ} (hx : 2 ≤ x) :
    (Finset.Icc 2 x).Nonempty :=
  ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩

/-- Maximum over natural endpoints `2 <= y <= x` of the reduced-residue maximum. -/
noncomputable def maxWeightedProgressionDiscrepancyUpTo
    (x q : ℕ) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y => maxWeightedProgressionDiscrepancy y q)
  else 0

/-- Vaughan's natural-endpoint logarithmic-window weighted contract. -/
def hasWeightedBombieriVinogradovWindow : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℕ, A + 4 < (B : ℝ) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x → ∀ Q : ℕ, 1 ≤ Q →
        (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
          (Real.log (x : ℝ)) ^ B →
          (∑ q ∈ Finset.Icc 1 Q,
            maxWeightedProgressionDiscrepancyUpTo x q) ≤
            C * (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) A

theorem chebyshevProgressionSum_eq_of_mod_eq
    {x q a b : ℕ} (h : a % q = b % q) :
    chebyshevProgressionSum x q a = chebyshevProgressionSum x q b := by
  simp only [chebyshevProgressionSum]
  congr 1
  ext n
  simp [h]

theorem chebyshevProgressionSum_one_zero (x : ℕ) :
    chebyshevProgressionSum x 1 0 = Chebyshev.psi (x : ℝ) := by
  rw [chebyshevProgressionSum, Chebyshev.psi, Nat.floor_natCast]
  have hfilter :
      (Finset.Icc 1 x).filter (fun n => n % 1 = 0 % 1) = Finset.Icc 1 x := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mod_one]
    tauto
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    simpa using Finset.Icc_succ_left_eq_Ioc 0 x
  rw [hfilter, hinterval]

theorem maxWeightedProgressionDiscrepancyUpTo_eq_sup_residues
    {x q : ℕ} (hx : 2 ≤ x) (hq : 0 < q) :
    maxWeightedProgressionDiscrepancyUpTo x q =
      (coprimeResidues q).sup' (coprimeResidues_nonempty hq) (fun a =>
        (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx) (fun y =>
          weightedProgressionDiscrepancy y q a)) := by
  rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx]
  simp_rw [maxWeightedProgressionDiscrepancy, dif_pos hq]
  exact Finset.sup'_comm (weightedEndpointRange_nonempty hx)
    (coprimeResidues_nonempty hq)
    (fun y a => weightedProgressionDiscrepancy y q a)

end BoundedGaps.Maynard
