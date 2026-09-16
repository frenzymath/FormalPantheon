import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# The starred endpoint weight in Perron's formula

This file implements the half-weight convention in
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.1, p. 138, as inherited by Theorem 5.2,
p. 139. Equality is taken after casting the natural index to the real cutoff,
so a nonintegral cutoff has no half-weighted term.
-/

namespace PrimesRestrictedDigits

/-- The starred Perron weight: one below the cutoff, one half at it, and zero
above it. -/
noncomputable def perronWeight (x : Real) (n : Nat) : Real :=
  if (n : Real) < x then 1 else if (n : Real) = x then 1 / 2 else 0

theorem perronWeight_eq_one_of_lt {x : Real} {n : Nat} (hnx : (n : Real) < x) :
    perronWeight x n = 1 := by
  simp [perronWeight, hnx]

theorem perronWeight_eq_half_of_eq {x : Real} {n : Nat} (hnx : (n : Real) = x) :
    perronWeight x n = 1 / 2 := by
  simp [perronWeight, hnx]

theorem perronWeight_eq_zero_of_lt {x : Real} {n : Nat} (hxn : x < (n : Real)) :
    perronWeight x n = 0 := by
  have hnlt : ¬(n : Real) < x := not_lt_of_ge hxn.le
  have hneq : ¬(n : Real) = x := ne_of_gt hxn
  simp [perronWeight, hnlt, hneq]

theorem perronWeight_eq_one_iff {x : Real} {n : Nat} :
    perronWeight x n = 1 ↔ (n : Real) < x := by
  constructor
  · intro h
    by_contra hnot
    have hle : x <= (n : Real) := le_of_not_gt hnot
    by_cases heq : (n : Real) = x
    · rw [perronWeight_eq_half_of_eq heq] at h
      norm_num at h
    · have hzero : perronWeight x n = 0 := by
        simp [perronWeight, not_lt_of_ge hle, heq]
      rw [hzero] at h
      norm_num at h
  · exact perronWeight_eq_one_of_lt

theorem perronWeight_eq_half_iff {x : Real} {n : Nat} :
    perronWeight x n = 1 / 2 ↔ (n : Real) = x := by
  constructor
  · intro h
    by_contra hne
    by_cases hlt : (n : Real) < x
    · rw [perronWeight_eq_one_of_lt hlt] at h
      norm_num at h
    · have hzero : perronWeight x n = 0 := by
        simp [perronWeight, hlt, hne]
      rw [hzero] at h
      norm_num at h
  · exact perronWeight_eq_half_of_eq

theorem perronWeight_eq_zero_iff {x : Real} {n : Nat} :
    perronWeight x n = 0 ↔ x < (n : Real) := by
  constructor
  · intro h
    by_contra hnot
    have hle : (n : Real) <= x := le_of_not_gt hnot
    by_cases heq : (n : Real) = x
    · rw [perronWeight_eq_half_of_eq heq] at h
      norm_num at h
    · have hone : perronWeight x n = 1 :=
        perronWeight_eq_one_of_lt (lt_of_le_of_ne hle heq)
      rw [hone] at h
      norm_num at h
  · exact perronWeight_eq_zero_of_lt

theorem perronWeight_nonneg (x : Real) (n : Nat) : 0 <= perronWeight x n := by
  by_cases hlt : (n : Real) < x
  · simp [perronWeight, hlt]
  · by_cases heq : (n : Real) = x
    · norm_num [perronWeight, hlt, heq]
    · simp [perronWeight, hlt, heq]

theorem perronWeight_le_one (x : Real) (n : Nat) : perronWeight x n <= 1 := by
  by_cases hlt : (n : Real) < x
  · simp [perronWeight, hlt]
  · by_cases heq : (n : Real) = x
    · norm_num [perronWeight, hlt, heq]
    · simp [perronWeight, hlt, heq]

end PrimesRestrictedDigits
