import Mathlib.Data.Nat.ChineseRemainder

/-!
# Simultaneous congruences as one CRT class

Maynard2013v3, Section 5 (source lines 273--280), identifies compatible
congruence conditions with one residue class modulo the product of the
pairwise-coprime moduli.  This file records that finite CRT step in the
list-indexed form supplied by Mathlib.
-/

namespace BoundedGaps.Maynard

open scoped Function

theorem modEq_crt_iff
    {ι : Type*} (a s : ι → ℕ) (l : List ι)
    (co : l.Pairwise (Nat.Coprime on s)) (z : ℕ) :
    z ≡ (Nat.chineseRemainderOfList a s l co : ℕ)
        [MOD (l.map s).prod] ↔
      ∀ i ∈ l, z ≡ a i [MOD s i] := by
  constructor
  · intro hz i hi
    have hproj := (Nat.modEq_list_map_prod_iff co).mp hz i hi
    have hcrt := (Nat.chineseRemainderOfList a s l co).property i hi
    exact hproj.trans hcrt
  · intro hz
    exact Nat.chineseRemainderOfList_modEq_unique a s l co hz

end BoundedGaps.Maynard
