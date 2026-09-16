import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Order

/-!
# Recursive bounds for finite coordinate tails

This file packages the reverse-induction range estimate used in Chen's English
Lemma 11 / Chinese Lemma 12 [CHEN1964-EN, p. 1567;
CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

/-- In a finite linear order, the open suffix after an embedded index is the
closed suffix beginning at its successor. -/
theorem Ioi_castSucc_eq_Ici_succ {n : Nat} (i : Fin n) :
    Finset.Ioi i.castSucc = Finset.Ici i.succ := by
  ext j
  simp only [Finset.mem_Ioi, Finset.mem_Ici]
  exact Fin.castSucc_lt_iff_succ_le

/-- The closed suffix at the last finite index is a singleton. -/
theorem Ici_last_eq_singleton (n : Nat) :
    Finset.Ici (Fin.last n) = ({Fin.last n} : Finset (Fin (n + 1))) := by
  ext j
  simp only [Finset.mem_Ici, Finset.mem_singleton]
  constructor
  · intro h
    apply Fin.ext
    simp only [Fin.val_last]
    change n ≤ j.val at h
    exact Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) h
  · rintro rfl
    exact le_rfl

/-- The open suffix after the last finite index is empty. -/
theorem Ioi_last_eq_empty (n : Nat) :
    Finset.Ioi (Fin.last n) = (∅ : Finset (Fin (n + 1))) := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨j, hj⟩
  have h : Fin.last n < j := Finset.mem_Ioi.mp hj
  have hj' : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  change n < j.val at h
  omega

/-- Local strict cap inequalities imply a strict cap for every closed suffix
sum. -/
theorem sum_Ici_lt_of_last_of_step {n : Nat}
    (upper cap : Fin (n + 1) → Nat)
    (hLast : upper (Fin.last n) < cap (Fin.last n))
    (hStep : ∀ i : Fin n,
      upper i.castSucc + cap i.succ < cap i.castSucc) (i : Fin (n + 1)) :
    (∑ j ∈ Finset.Ici i, upper j) < cap i := by
  induction i using Fin.reverseInduction with
  | last =>
      rw [Ici_last_eq_singleton]
      simpa using hLast
  | cast i ih =>
      rw [Finset.Ici_eq_cons_Ioi, Finset.sum_cons,
        Ioi_castSucc_eq_Ici_succ]
      exact (Nat.add_lt_add_left ih _).trans (hStep i)

/-- The same recursive hypotheses bound the open suffix after a nonfinal
coordinate by the next cap. -/
theorem sum_Ioi_castSucc_lt_of_last_of_step {n : Nat}
    (upper cap : Fin (n + 1) → Nat)
    (hLast : upper (Fin.last n) < cap (Fin.last n))
    (hStep : ∀ i : Fin n,
      upper i.castSucc + cap i.succ < cap i.castSucc) (i : Fin n) :
    (∑ j ∈ Finset.Ioi i.castSucc, upper j) < cap i.succ := by
  rw [Ioi_castSucc_eq_Ici_succ]
  exact sum_Ici_lt_of_last_of_step upper cap hLast hStep i.succ

/-- A closed suffix sum of natural lower bounds is at least its first
coordinate. -/
theorem le_sum_Ici {n : Nat} (lower : Fin (n + 1) → Nat) (i : Fin (n + 1)) :
    lower i ≤ ∑ j ∈ Finset.Ici i, lower j := by
  rw [Finset.Ici_eq_cons_Ioi, Finset.sum_cons]
  exact Nat.le_add_right _ _

/-- The open suffix after a nonfinal coordinate contains the next lower
endpoint. -/
theorem le_sum_Ioi_castSucc {n : Nat}
    (lower : Fin (n + 1) → Nat) (i : Fin n) :
    lower i.succ ≤ ∑ j ∈ Finset.Ioi i.castSucc, lower j := by
  rw [Ioi_castSucc_eq_Ici_succ]
  exact le_sum_Ici lower i.succ

end Waring.LargeNumber
