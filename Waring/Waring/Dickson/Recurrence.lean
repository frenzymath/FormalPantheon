import Waring.Dickson.NthRootGap

/-!
# Dickson's interval-length recurrence

This file formalizes recurrence (7) and the logarithmic closed form (8) from
[DICKSON1933, p. 711].
-/

namespace Waring

/-- One step of Dickson's interval-length recurrence. -/
noncomputable def dicksonLengthStep (n : Nat) (nu length : Real) : Real :=
  (nu * length) ^ ((n : Real) / ((n - 1 : Nat) : Real))

/-- Dickson's interval length after `t` ascent steps. -/
noncomputable def dicksonLength (n : Nat) (nu initial : Real) : Nat → Real
  | 0 => initial
  | t + 1 => dicksonLengthStep n nu (dicksonLength n nu initial t)

/-- Positive recurrence data give positive interval lengths at every step. -/
theorem dicksonLength_pos {n : Nat} {nu initial : Real}
    (hnu : 0 < nu) (hinitial : 0 < initial) (t : Nat) :
    0 < dicksonLength n nu initial t := by
  induction t with
  | zero => exact hinitial
  | succ t ih =>
      exact Real.rpow_pos_of_pos (mul_pos hnu ih) _

/-- Dickson's closed logarithmic formula for recurrence (7), printed as (8) in
[DICKSON1933, p. 711]. -/
theorem log_dicksonLength {n : Nat} (hn : 1 < n) {nu initial : Real}
    (hnu : 0 < nu) (hinitial : 0 < initial) (t : Nat) :
    Real.log (dicksonLength n nu initial t) =
      ((n : Real) / ((n - 1 : Nat) : Real)) ^ t *
          (Real.log initial + (n : Real) * Real.log nu) -
        (n : Real) * Real.log nu := by
  have hnOne : 1 ≤ n := hn.le
  have hdenom : ((n - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hn).ne'
  have hdenom' : (n : Real) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  have hfixed :
      ((n : Real) / ((n - 1 : Nat) : Real)) * (1 - (n : Real)) = -(n : Real) := by
    rw [Nat.cast_sub hnOne, Nat.cast_one]
    field_simp [hdenom']
    ring
  induction t with
  | zero => simp [dicksonLength]
  | succ t ih =>
      rw [dicksonLength, dicksonLengthStep,
        Real.log_rpow (mul_pos hnu (dicksonLength_pos hnu hinitial t)),
        Real.log_mul hnu.ne' (dicksonLength_pos hnu hinitial t).ne', ih]
      rw [pow_succ]
      calc
        (n : Real) / ((n - 1 : Nat) : Real) *
            (Real.log nu + (
              ((n : Real) / ((n - 1 : Nat) : Real)) ^ t *
                  (Real.log initial + (n : Real) * Real.log nu) -
                (n : Real) * Real.log nu)) =
            ((n : Real) / ((n - 1 : Nat) : Real)) ^ t *
                ((n : Real) / ((n - 1 : Nat) : Real)) *
                  (Real.log initial + (n : Real) * Real.log nu) +
              (((n : Real) / ((n - 1 : Nat) : Real)) * (1 - (n : Real))) *
                Real.log nu := by ring
        _ = ((n : Real) / ((n - 1 : Nat) : Real)) ^ t *
              ((n : Real) / ((n - 1 : Nat) : Real)) *
                (Real.log initial + (n : Real) * Real.log nu) -
              (n : Real) * Real.log nu := by rw [hfixed]; ring

end Waring
