import Mathlib
import Waring.Main

namespace Waring.Comparator

open scoped BigOperators

def HasPowerSumRepresentation (k s n : Nat) : Prop :=
  ∃ x : Fin s → Nat, n = ∑ i, x i ^ k

def IsUniversalWaringBound (k s : Nat) : Prop :=
  ∀ n : Nat, 0 < n → HasPowerSumRepresentation k s n

def IsLeastUniversalWaringBound (k s : Nat) : Prop :=
  IsUniversalWaringBound k s ∧
    ∀ t : Nat, IsUniversalWaringBound k t → s ≤ t

def MainTheorem : Prop := IsLeastUniversalWaringBound 5 37

theorem g_five_eq_thirtySeven : MainTheorem := by
  exact Waring.Main.g_five_eq_thirtySeven

end Waring.Comparator
