import PrimesRestrictedDigits.MajorArcs.WeightedPhaseSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient

/-!
# Residue decomposition of weighted phase sums

This is the neutral module for the reduced residue carrier and the finite residue
decomposition shared by the major-arc classes.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The complete reduced residue system, including `0` when `q=1`. -/
def majorArcReducedResidues (q : Nat) : Finset Nat :=
  (Finset.range q).filter fun r => Nat.Coprime r q

theorem card_majorArcReducedResidues (q : Nat) :
    (majorArcReducedResidues q).card = Nat.totient q := by
  rw [majorArcReducedResidues, Nat.totient_eq_card_coprime]
  congr 1
  ext r
  simp [Nat.coprime_comm]

/-- The weight in one congruence class on a finite carrier. -/
noncomputable def majorArcResidueWeightSum
    (s : Finset Nat) (w : Nat → Complex) (q r : Nat) : Complex :=
  ∑ n ∈ s with n ≡ r [MOD q], w n

/-- A signed rational weighted phase sum is exactly the sum of its residue
fibers. -/
theorem majorArcWeightedPhaseSum_rat_eq_sum_residues
    (s : Finset Nat) (w : Nat → Complex)
    {q : Nat} (hq : 0 < q) (b : Int) :
    majorArcWeightedPhaseSum s w ((b : Real) / (q : Real)) =
      ∑ r ∈ Finset.range q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          majorArcResidueWeightSum s w q r := by
  unfold majorArcWeightedPhaseSum majorArcResidueWeightSum
  have hmaps : ∀ n ∈ s, n % q ∈ Finset.range q := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.mod_lt n hq)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => w n *
      majorArcPhase ((n : Real) * ((b : Real) / (q : Real))))]
  apply Finset.sum_congr rfl
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  rw [Finset.mul_sum]
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hrq]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmod : n % q = r := (Finset.mem_filter.mp hn).2
  have hmod : n ≡ r [MOD q] := by
    change n % q = r % q
    rw [Nat.mod_eq_of_lt hrq]
    exact hnmod
  have hphase := majorArcPhase_int_of_modEq hq b hmod
  rw [show majorArcPhase ((n : Real) * ((b : Real) / (q : Real))) =
      majorArcPhase ((n : Real) * (b : Real) / (q : Real)) by
        congr 1
        ring,
    hphase, mul_comm]

end PrimesRestrictedDigits
