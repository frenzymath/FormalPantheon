import Waring.Dickson.Basic

/-!
# Packed reachability certificates

Natural numbers are used as finite bitsets. Bit `target` records that the
target was reached by the bounded power-sum recurrence.
-/

namespace Waring.Certificate

open Waring Waring.Statement

/-- A mask retaining exactly bit positions from zero through `upper`. -/
def reachabilityMask (upper : Nat) : Nat := 2 ^ (upper + 1) - 1

/-- A bit mask for the inclusive natural interval `[lower, upper]`. -/
def intervalMask (lower upper : Nat) : Nat :=
  (2 ^ (upper - lower + 1) - 1) <<< lower

/-- The union of shifts of `previous` by `a^k` for every `a` in `bases`. -/
def addPowerShifts (k previous : Nat) : List Nat → Nat
  | [] => 0
  | a :: bases => (previous <<< a ^ k) ||| addPowerShifts k previous bases

/-- Packed targets reachable with `slots` powers, capped at `upper`, using bases
strictly below `baseLimit`. -/
def powerReachability (k upper baseLimit : Nat) : Nat → Nat
  | 0 => 1
  | slots + 1 =>
      reachabilityMask upper &&&
        addPowerShifts k (powerReachability k upper baseLimit slots)
          (List.range baseLimit)

private theorem testBit_addPowerShifts {k previous target : Nat} {bases : List Nat}
    (hbit : (addPowerShifts k previous bases).testBit target = true) :
    ∃ a ∈ bases, a ^ k ≤ target ∧ previous.testBit (target - a ^ k) = true := by
  induction bases with
  | nil => simp [addPowerShifts] at hbit
  | cons a bases ih =>
      rw [addPowerShifts, Nat.testBit_lor, Bool.or_eq_true] at hbit
      rcases hbit with hshift | hrest
      · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at hshift
        exact ⟨a, by simp, of_decide_eq_true hshift.1, hshift.2⟩
      · obtain ⟨b, hb, hbPower, hbBit⟩ := ih hrest
        exact ⟨b, by simp [hb], hbPower, hbBit⟩

/-- Every set bit of the packed recurrence yields a kernel-checked power-sum
representation. This is the soundness bridge for finite coverage certificates.
-/
theorem powerReachability_sound {k upper baseLimit slots target : Nat}
    (hbit : (powerReachability k upper baseLimit slots).testBit target = true) :
    HasPowerSumRepresentation k slots target := by
  induction slots generalizing target with
  | zero =>
      have htarget : target = 0 :=
        Nat.testBit_one_eq_true_iff_self_eq_zero.mp (by simpa [powerReachability] using hbit)
      subst target
      exact ⟨fun i ↦ Fin.elim0 i, by simp⟩
  | succ slots ih =>
      have hshifted :
          (addPowerShifts k (powerReachability k upper baseLimit slots)
              (List.range baseLimit)).testBit target = true := by
        rw [powerReachability, Nat.testBit_land, Bool.and_eq_true] at hbit
        exact hbit.2
      obtain ⟨a, _haRange, haPower, haBit⟩ := testBit_addPowerShifts hshifted
      have hprevious := ih haBit
      simpa [Nat.sub_add_cancel haPower] using
        HasPowerSumRepresentation.addPower hprevious a

/-- Every bit belonging to an inclusive interval is set in its interval mask. -/
theorem testBit_intervalMask {lower upper target : Nat}
    (hlower : lower ≤ target) (hupper : target ≤ upper) :
    (intervalMask lower upper).testBit target = true := by
  rw [intervalMask, Nat.testBit_shiftLeft, Bool.and_eq_true,
    Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  omega

/-- A closed bit-mask coverage equality proves representation coverage of the
corresponding inclusive interval. -/
theorem representsOn_of_reachabilityMask {k cap baseLimit slots lower upper : Nat}
    (hcoverage :
      powerReachability k cap baseLimit slots &&& intervalMask lower upper =
        intervalMask lower upper) :
    RepresentsOn k slots lower upper := by
  intro target hlower hupper
  have hmask := testBit_intervalMask hlower hupper
  have hbits := congrArg (fun bits : Nat ↦ bits.testBit target) hcoverage
  rw [Nat.testBit_land, hmask] at hbits
  exact powerReachability_sound (by simpa using hbits)

end Waring.Certificate
