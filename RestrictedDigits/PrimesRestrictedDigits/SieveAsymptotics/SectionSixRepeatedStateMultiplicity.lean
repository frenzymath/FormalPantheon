import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSquareTail
import Mathlib.Tactic.NormNum

/-!
# Finite multiplicity interface for repeated-state charges

This is the exact finite bookkeeping theorem needed to sum the pointwise `q^2` charges. The
factorization-specific fiber bound is deliberately a hypothesis of this interface and remains
a separate node.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The pointwise charge attached to a repeated prime square. -/
def sectionSixRepeatedSquareCharge
    (digit : Fin 10) (length q : Nat) : Real :=
  |realTypeIProgressionError digit length (q * q)| +
    ((typeIProgressionDensity digit : Real) +
      (restrictedDigitDensity digit : Real)) *
      ((paddedRestrictedNumbers digit length).card : Real) /
        (q * q : Real)

theorem sectionSixRepeatedSquareCharge_nonneg
    (digit : Fin 10) (length q : Nat) :
    0 ≤ sectionSixRepeatedSquareCharge digit length q := by
  unfold sectionSixRepeatedSquareCharge
  have hprog : 0 ≤ (typeIProgressionDensity digit : Real) := by
    rw [typeIProgressionDensity_eq]
    split_ifs <;> norm_num
  have hA : 0 ≤ (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  positivity

theorem abs_sectionSixWeakSiftedSum_le_squareCharge
    (digit : Fin 10) (length : Nat) (d : PNat) {q : Nat}
    (hq : q.Prime) {z : Real} (hz : 5 < z) (hqz : z < (q : Real))
    (hd : (d : Nat).Coprime 10) :
    |sectionSixWeakSiftedSum digit length
        ((d * Nat.toPNat' q) * Nat.toPNat' q) (q : Real)| ≤
      sectionSixRepeatedSquareCharge digit length q := by
  exact abs_sectionSixWeakSiftedSum_le_repeatedSquare
    digit length d hq hz hqz hd

theorem sum_abs_value_le_cardinality_charge_of_fiber_card
    {α : Type*} (states : Finset α) (Q : Finset Nat)
    (q : α → Nat) (value : α → Real) (charge : Nat → Real) (K : Nat)
    (hmap : ∀ s, s ∈ states → q s ∈ Q)
    (hfiber : ∀ r, r ∈ Q →
      (states.filter (fun s => q s = r)).card ≤ K)
    (hpoint : ∀ s, s ∈ states → |value s| ≤ charge (q s))
    (hcharge : ∀ r, r ∈ Q → 0 ≤ charge r) :
    (∑ s ∈ states, |value s|) ≤
      (K : Real) * ∑ r ∈ Q, charge r := by
  classical
  have hpointSum :
      (∑ s ∈ states, |value s|) ≤
        ∑ s ∈ states, charge (q s) := by
    apply Finset.sum_le_sum
    intro s hs
    exact hpoint s hs
  have hfiberSum (r : Nat) (hr : r ∈ Q) :
      (∑ s ∈ states with q s = r, charge (q s)) =
        ((states.filter (fun s => q s = r)).card : Real) * charge r := by
    calc
      (∑ s ∈ states with q s = r, charge (q s)) =
          ∑ s ∈ states with q s = r, charge r := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_filter] at hs
        exact congrArg charge hs.2
      _ = ((states.filter (fun s => q s = r)).card : Real) * charge r := by
        simp [nsmul_eq_mul]
  have hfiberBound (r : Nat) (hr : r ∈ Q) :
      (∑ s ∈ states with q s = r, charge (q s)) ≤
        (K : Real) * charge r := by
    rw [hfiberSum r hr]
    have hcard :
        ((states.filter (fun s => q s = r)).card : Real) ≤ (K : Real) := by
      exact_mod_cast hfiber r hr
    exact mul_le_mul_of_nonneg_right hcard (hcharge r hr)
  calc
    (∑ s ∈ states, |value s|) ≤ ∑ s ∈ states, charge (q s) := hpointSum
    _ = ∑ r ∈ Q, ∑ s ∈ states with q s = r, charge (q s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmap (fun s => charge (q s))
    _ ≤ ∑ r ∈ Q, (K : Real) * charge r := by
      apply Finset.sum_le_sum
      intro r hr
      exact hfiberBound r hr
    _ = (K : Real) * ∑ r ∈ Q, charge r := by
      rw [Finset.mul_sum]

end

end PrimesRestrictedDigits
