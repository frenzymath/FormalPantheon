import Mathlib

/-!
# The statement `g(5) = 37`

This file is the complete semantic review surface for the main result. It has no
project imports.

A representation uses exactly `s` slots indexed by `Fin s`, but its entries are
natural numbers and may therefore be zero. Deleting zero entries turns such a
representation into a sum of at most `s` positive `k`th powers. Conversely, any
sum of at most `s` positive `k`th powers can be padded with zero entries, so this
is the standard "at most `s`" convention for the classical Waring number.
-/

namespace Waring.Statement

/-- `n` is a sum of `s` many `k`th powers of natural numbers. Zero summands are
allowed, so the fixed number of slots expresses an at-most bound. -/
def HasPowerSumRepresentation (k s n : Nat) : Prop :=
  ∃ x : Fin s → Nat, n = ∑ i, x i ^ k

/-- Every positive natural number is a sum of at most `s` many `k`th powers. -/
def IsUniversalWaringBound (k s : Nat) : Prop :=
  ∀ n : Nat, 0 < n → HasPowerSumRepresentation k s n

/-- `s` is the least universal Waring bound for exponent `k`. -/
def IsLeastUniversalWaringBound (k s : Nat) : Prop :=
  IsUniversalWaringBound k s ∧
    ∀ t : Nat, IsUniversalWaringBound k t → s ≤ t

/-- The classical Waring statement `g(5) = 37`: every positive natural number
is a sum of at most 37 fifth powers, and no smaller uniform bound works. -/
def MainTheorem : Prop :=
  IsLeastUniversalWaringBound 5 37

end Waring.Statement
