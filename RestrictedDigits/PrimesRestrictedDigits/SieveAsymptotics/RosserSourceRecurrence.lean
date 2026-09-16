import PrimesRestrictedDigits.SieveAsymptotics.RosserCutoffRecurrence

/-!
# Source-facing finite Rosser recurrences

These declarations retain Iwaniec's printed logarithmic ratio variable and domains around
equations (4.4)--(4.5). The finite combinatorial cores have fewer hypotheses; the additional
assumptions here document the exact source specialization.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Iwaniec's beta-two equation (4.4), including the printed weak root and
strict upper cutoff. -/
theorem iwaniecRosserEquation_four_four
    (P : Finset Nat) (nu : Nat → Real) (level z s : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (_hz : 2 ≤ z)
    (hR : 0 < R) (_hs : s = Real.log level / Real.log z)
    (_hsLower : 2 ≤ s) :
    lowerRosserFailurePartialSum P nu level z R =
      ∑ p ∈ P.filter (fun p : Nat ↦
        rosserCutoffRoot level (2 + 2 * R) ≤ (p : Real) ∧
          (p : Real) < z),
        nu p * upperRosserFailurePartialSum P nu (level / p) p (R - 1) := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using
    (lowerRosserFailurePartialSum_succ_eq_sum_upper
      P nu level z R hprime (by positivity))

/-- Every inner problem in equation (4.4) lies in the source's ratio-greater-
than-one domain. -/
theorem iwaniecRosserEquation_four_four_innerDomains
    (P : Finset Nat) (level z s : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (hz : 2 ≤ z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 ≤ s)
    {p : Nat} (hpP : p ∈ P) (hpz : (p : Real) < z) :
    z < level / (p : Real) ∧
      1 < Real.log (level / (p : Real)) / Real.log (p : Real) := by
  apply rosserInnerDomains_of_two_le_logRatio hlevel hz
    (hprime p hpP) hpz
  rw [← hs]
  exact hsLower

/-- Iwaniec's beta-two equation (4.5), including the printed weak root and
strict upper cutoff. -/
theorem iwaniecRosserEquation_four_five
    (P : Finset Nat) (nu : Nat → Real) (level z s : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (hz : 2 ≤ z)
    (_hR : 0 < R) (hs : s = Real.log level / Real.log z)
    (hsLower : 3 ≤ s) :
    upperRosserFailurePartialSum P nu level z R =
      ∑ p ∈ P.filter (fun p : Nat ↦
        rosserCutoffRoot level (3 + 2 * R) ≤ (p : Real) ∧
          (p : Real) < z),
        nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  have hratio : (3 : Real) ≤ Real.log level / Real.log z := by
    rw [← hs]
    exact hsLower
  have hcube := power_le_of_natCast_le_log_div_log hlevel hz hratio
  simpa only [Nat.add_comm] using
    (upperRosserFailurePartialSum_eq_sum_lower
      P nu level z R hprime (by positivity) hcube)

/-- Every inner problem in equation (4.5) lies in the source's ratio-greater-
than-two domain. -/
theorem iwaniecRosserEquation_four_five_innerDomains
    (P : Finset Nat) (level z s : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (hz : 2 ≤ z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 ≤ s)
    {p : Nat} (hpP : p ∈ P) (hpz : (p : Real) < z) :
    z ^ 2 < level / (p : Real) ∧
      2 < Real.log (level / (p : Real)) / Real.log (p : Real) := by
  apply rosserInnerDomains_of_three_le_logRatio hlevel hz
    (hprime p hpP) hpz
  rw [← hs]
  exact hsLower

end PrimesRestrictedDigits
