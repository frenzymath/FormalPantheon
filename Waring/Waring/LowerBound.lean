import Waring.Statement

/-!
# The elementary lower bound for `g(5)`

The positive integer 223 cannot be represented with fewer than 37 fifth-power
slots. Chen records the historical lower bound `37 <= g(5)` at
[CHEN1964-EN, p. 1547]; the proof here verifies the elementary obstruction
directly.
-/

namespace Waring

open scoped BigOperators
open Statement

/-- Every representation of 223 as a sum of fifth powers has at least 37 slots. -/
theorem representation_223_requires_thirtySeven {s : Nat} {x : Fin s → Nat}
    (h : 223 = ∑ i, x i ^ 5) : 37 ≤ s := by
  have hx_le_two (i : Fin s) : x i ≤ 2 := by
    have hterm_le : x i ^ 5 ≤ 223 := by
      rw [h]
      exact Finset.single_le_sum (f := fun j : Fin s ↦ x j ^ 5)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    by_contra hnot
    have hthree : 3 ≤ x i := by omega
    have hpow := Nat.pow_le_pow_left hthree 5
    norm_num at hpow
    omega

  let a : Nat := ∑ i, if x i = 2 then 1 else 0
  let c : Nat := ∑ i, if x i = 0 then 0 else 1

  have ha_le_c : a ≤ c := by
    dsimp [a, c]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : x i = 2 <;> simp [hi]

  have hc_le_s : c ≤ s := by
    calc
      c = ∑ i : Fin s, if x i = 0 then 0 else 1 := rfl
      _ ≤ ∑ _i : Fin s, (1 : Nat) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : x i = 0 <;> simp [hi]
      _ = s := by simp

  have hentry (i : Fin s) :
      x i ^ 5 = 31 * (if x i = 2 then 1 else 0) + (if x i = 0 then 0 else 1) := by
    have hi := hx_le_two i
    interval_cases hx : x i <;> norm_num [hx]

  have hcount : 223 = 31 * a + c := by
    calc
      223 = ∑ i, x i ^ 5 := h
      _ = ∑ i, (31 * (if x i = 2 then 1 else 0) +
          (if x i = 0 then 0 else 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hentry i
      _ = 31 * a + c := by
        simp only [a, c, Finset.sum_add_distrib, ← Finset.mul_sum]

  omega

/-- Any universal fifth-power Waring bound is at least 37. -/
theorem universal_bound_five_ge_thirtySeven {s : Nat}
    (hs : IsUniversalWaringBound 5 s) : 37 ≤ s := by
  obtain ⟨x, hx⟩ := hs 223 (by norm_num)
  exact representation_223_requires_thirtySeven hx

end Waring
