import Waring.Basic

/-!
# Dickson interval-ascent infrastructure

This file contains the discrete representation step underlying Theorems 11 and
12 of [DICKSON1933, pp. 710-711]. Root estimates that establish its remainder
hypothesis belong in later modules.
-/

namespace Waring

open scoped BigOperators
open Statement

/-- Every natural number in the inclusive interval `[lower, upper]` has the
given fixed-slot power-sum representation. -/
def RepresentsOn (k slots lower upper : Nat) : Prop :=
  ∀ n : Nat, lower ≤ n → n ≤ upper → HasPowerSumRepresentation k slots n

/-- Appending one base appends its power to a fixed-slot representation. -/
theorem HasPowerSumRepresentation.addPower {k slots n : Nat}
    (h : HasPowerSumRepresentation k slots n) (a : Nat) :
    HasPowerSumRepresentation k (slots + 1) (n + a ^ k) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Fin.cons a x, ?_⟩
  simp [Fin.sum_univ_succ, hx, Nat.add_comm]

/-- Dickson's discrete ascent step: one additional power covers a larger
interval when subtracting a suitable power always returns to the base interval.
-/
theorem representsOn_succ_of_remainders {k slots lower baseUpper newUpper : Nat}
    (hbase : RepresentsOn k slots lower baseUpper)
    (hremainder : ∀ n : Nat, lower ≤ n → n ≤ newUpper →
      ∃ a : Nat, a ^ k ≤ n ∧ lower ≤ n - a ^ k ∧ n - a ^ k ≤ baseUpper) :
    RepresentsOn k (slots + 1) lower newUpper := by
  intro n hnLower hnUpper
  obtain ⟨a, ha, hremLower, hremUpper⟩ := hremainder n hnLower hnUpper
  have hrem : HasPowerSumRepresentation k slots (n - a ^ k) :=
    hbase (n - a ^ k) hremLower hremUpper
  simpa [Nat.sub_add_cancel ha] using HasPowerSumRepresentation.addPower hrem a

end Waring
