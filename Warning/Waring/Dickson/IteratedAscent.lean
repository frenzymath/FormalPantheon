import Waring.Dickson.IntervalAscent
import Waring.Dickson.Recurrence

/-!
# Dickson's iterated interval ascent

This file proves the finite induction in Theorem 12 of
[DICKSON1933, p. 711].
-/

namespace Waring

open Statement

/-- Every natural number in the interval from `lower` through the real endpoint
`upper` has the given fixed-slot power-sum representation. -/
def RepresentsThrough (k slots lower : Nat) (upper : Real) : Prop :=
  forall target : Nat, lower <= target -> (target : Real) <= upper ->
    HasPowerSumRepresentation k slots target

/-- If the first Dickson recurrence step does not decrease the initial value,
then all recurrence values form a monotone sequence. -/
theorem dicksonLength_monotone {n : Nat} (hn : 1 < n) {nu initial : Real}
    (hnu : 0 < nu) (hinitial : 0 < initial)
    (hfirst : initial <= dicksonLength n nu initial 1) :
    Monotone (dicksonLength n nu initial) := by
  have hexponentNonneg :
      0 <= (n : Real) / ((n - 1 : Nat) : Real) := by
    positivity
  apply monotone_nat_of_le_succ
  intro t
  induction t with
  | zero => simpa [dicksonLength] using hfirst
  | succ t ih =>
      change dicksonLengthStep n nu (dicksonLength n nu initial t) <=
        dicksonLengthStep n nu (dicksonLength n nu initial (t + 1))
      rw [dicksonLengthStep, dicksonLengthStep]
      exact Real.rpow_le_rpow
        (mul_nonneg hnu.le (dicksonLength_pos hnu hinitial t).le)
        (mul_le_mul_of_nonneg_left ih hnu.le) hexponentNonneg

/-- One recurrence step transports representations between real endpoints.
The proof explicitly uses `Nat.floor current` as the inclusive natural base
endpoint before applying `dickson_interval_ascent`; no floor convention occurs
in the statement. -/
theorem RepresentsThrough.dicksonStep {n slots lower : Nat}
    {nu current : Real} (hn : 1 < n) (hnu : 0 < nu)
    (hcurrent : 0 < current)
    (hlowerNext : (lower : Real) <= dicksonLengthStep n nu current)
    (havailable :
      (lower : Real) + (n : Real) * nu * current <= current)
    (hrep : RepresentsThrough n slots lower current) :
    RepresentsThrough n (slots + 1) lower
      (dicksonLengthStep n nu current) := by
  have hnRealPos : 0 < (n : Real) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hLPos : 0 < (n : Real) * nu * current := by positivity
  have hbase : RepresentsOn n slots lower (Nat.floor current) := by
    intro target htargetLower htargetUpper
    apply hrep target htargetLower
    exact (Nat.cast_le.mpr htargetUpper).trans (Nat.floor_le hcurrent.le)
  apply dickson_interval_ascent (n := n) (slots := slots) (lower := lower)
    (baseUpper := Nat.floor current) (L := (n : Real) * nu * current)
    (sigma := dicksonLengthStep n nu current) hn hLPos
  · rw [dicksonLengthStep]
    congr 1
    field_simp
  · exact hlowerNext
  · refine havailable.trans ?_
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one current).le
  · exact hbase

/-- Dickson's Theorem 12: starting with a natural inclusive base interval,
each recurrence step adds one `n`th power and extends coverage through the
corresponding real endpoint.

The equation for `nu` is Dickson's definition before recurrence (7), and
`hfirst` is his hypothesis `L_1 >= L_0`. The endpoint hypothesis
`initial < baseUpper + 1` says exactly that the natural base interval contains
every natural target at most `initial`.
-/
theorem dickson_iterated_ascent {n slots lower baseUpper : Nat}
    {nu initial : Real} (hn : 1 < n) (hnu : 0 < nu)
    (hinitial : 0 < initial) (hlowerInitial : (lower : Real) < initial)
    (hnuDef :
      nu = (1 - (lower : Real) / initial) / (n : Real))
    (hfirst : initial <= dicksonLength n nu initial 1)
    (hbaseEndpoint : initial < ((baseUpper + 1 : Nat) : Real))
    (hbase : RepresentsOn n slots lower baseUpper) (t : Nat) :
    RepresentsThrough n (slots + t) lower
      (dicksonLength n nu initial t) := by
  have hnRealPos : 0 < (n : Real) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlengthMono : Monotone (dicksonLength n nu initial) :=
    dicksonLength_monotone hn hnu hinitial hfirst
  have hinitialLength (j : Nat) :
      initial <= dicksonLength n nu initial j := by
    simpa [dicksonLength] using hlengthMono (Nat.zero_le j)
  induction t with
  | zero =>
      intro target htargetLower htargetInitial
      have htargetSucc : target < baseUpper + 1 := by
        exact_mod_cast htargetInitial.trans_lt hbaseEndpoint
      simpa [dicksonLength] using
        hbase target htargetLower (Nat.lt_add_one_iff.mp htargetSucc)
  | succ t ih =>
      have hcurrentPos : 0 < dicksonLength n nu initial t :=
        dicksonLength_pos hnu hinitial t
      have hlowerNext :
          (lower : Real) <= dicksonLengthStep n nu
            (dicksonLength n nu initial t) := by
        rw [← dicksonLength]
        exact hlowerInitial.le.trans (hinitialLength (t + 1))
      have hratioNonneg : 0 <= (lower : Real) / initial :=
        div_nonneg (Nat.cast_nonneg lower) hinitial.le
      have hratioCurrent :
          (lower : Real) <=
            ((lower : Real) / initial) *
              dicksonLength n nu initial t := by
        calc
          (lower : Real) = ((lower : Real) / initial) * initial := by
            field_simp
          _ <= ((lower : Real) / initial) *
              dicksonLength n nu initial t :=
            mul_le_mul_of_nonneg_left (hinitialLength t) hratioNonneg
      have hnuScale :
          (n : Real) * nu = 1 - (lower : Real) / initial := by
        rw [hnuDef]
        field_simp
      have havailable :
          (lower : Real) + (n : Real) * nu *
              dicksonLength n nu initial t <=
            dicksonLength n nu initial t := by
        rw [hnuScale]
        calc
          (lower : Real) +
                (1 - (lower : Real) / initial) *
                  dicksonLength n nu initial t =
              (lower : Real) + dicksonLength n nu initial t -
                ((lower : Real) / initial) *
                  dicksonLength n nu initial t := by ring
          _ <= dicksonLength n nu initial t := by linarith
      have hstep := RepresentsThrough.dicksonStep hn hnu hcurrentPos
        hlowerNext havailable ih
      simpa [dicksonLength, Nat.add_assoc] using hstep

end Waring
