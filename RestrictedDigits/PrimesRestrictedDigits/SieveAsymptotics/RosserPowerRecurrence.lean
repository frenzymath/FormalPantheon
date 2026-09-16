import PrimesRestrictedDigits.SieveAsymptotics.RosserPartialRecurrence

/-!
# Weak-root support in the finite Rosser recurrences

The unrestricted partial-sum recurrences are restricted to Iwaniec's printed weak lower
endpoints. The omitted outer terms vanish by the maximal-rank cutoff-power bounds.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Equation (4.4) with the weak endpoint written as a natural-power
condition. -/
theorem lowerRosserFailurePartialSum_succ_eq_sum_upper_of_headPow
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailurePartialSum P nu level z (R + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦
        level ≤ (p : Real) ^ (2 * (R + 1) + 2) ∧ (p : Real) < z),
        nu p * upperRosserFailurePartialSum P nu (level / p) p R := by
  rw [lowerRosserFailurePartialSum_succ_eq_sum_upper_unrestricted
    P nu level z R hprime]
  symm
  apply Finset.sum_subset
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpData.1, hpData.2.2⟩
  · intro p hpOuter hpNotInner
    have hpData := Finset.mem_filter.mp hpOuter
    have hpPrime := hprime p hpData.1
    have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hpOne : 1 ≤ (p : Real) := by exact_mod_cast hpPrime.one_le
    have hnotPower :
        ¬level ≤ (p : Real) ^ (2 * (R + 1) + 2) := by
      intro hpower
      exact hpNotInner (Finset.mem_filter.mpr
        ⟨hpData.1, hpower, hpData.2⟩)
    have hmul : (p : Real) ^ (2 * R + 3) * p ≤ level := by
      calc
        (p : Real) ^ (2 * R + 3) * p =
            (p : Real) ^ (2 * (R + 1) + 2) := by
          rw [← pow_succ]
          congr 1
        _ ≤ level := (lt_of_not_ge hnotPower).le
    have hdiv : (p : Real) ^ (2 * R + 3) ≤ level / p :=
      (le_div_iff₀ hpPos).mpr hmul
    rw [upperRosserFailurePartialSum_eq_zero_of_cutoffPow_le
      P nu (level / p) p R hprime hpOne hdiv]
    ring

/-- Equation (4.5) with the weak endpoint written as a natural-power
condition. -/
theorem upperRosserFailurePartialSum_eq_sum_lower_of_headPow
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hcube : z ^ 3 ≤ level) :
    upperRosserFailurePartialSum P nu level z R =
      ∑ p ∈ P.filter (fun p : Nat ↦
        level ≤ (p : Real) ^ (2 * R + 3) ∧ (p : Real) < z),
        nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  rw [upperRosserFailurePartialSum_eq_sum_lower_of_cube_le
    P nu level z R hprime hcube]
  symm
  apply Finset.sum_subset
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpData.1, hpData.2.2⟩
  · intro p hpOuter hpNotInner
    have hpData := Finset.mem_filter.mp hpOuter
    have hpPrime := hprime p hpData.1
    have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hpOne : 1 ≤ (p : Real) := by exact_mod_cast hpPrime.one_le
    have hnotPower : ¬level ≤ (p : Real) ^ (2 * R + 3) := by
      intro hpower
      exact hpNotInner (Finset.mem_filter.mpr
        ⟨hpData.1, hpower, hpData.2⟩)
    have hmul : (p : Real) ^ (2 * R + 2) * p ≤ level := by
      calc
        (p : Real) ^ (2 * R + 2) * p =
            (p : Real) ^ (2 * R + 3) := by
          rw [← pow_succ]
        _ ≤ level := (lt_of_not_ge hnotPower).le
    have hdiv : (p : Real) ^ (2 * R + 2) ≤ level / p :=
      (le_div_iff₀ hpPos).mpr hmul
    rw [lowerRosserFailurePartialSum_eq_zero_of_cutoffPow_le
      P nu (level / p) p R hprime hpOne hdiv]
    ring

/-- Iwaniec's equation (4.4), with its weak root endpoint explicit. The total
lower rank is `R + 1`, so the inner upper sum ends at rank `R`. -/
theorem lowerRosserFailurePartialSum_succ_eq_sum_upper
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 0 ≤ level) :
    lowerRosserFailurePartialSum P nu level z (R + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦
        rosserCutoffRoot level (2 * (R + 1) + 2) ≤ (p : Real) ∧
          (p : Real) < z),
        nu p * upperRosserFailurePartialSum P nu (level / p) p R := by
  rw [lowerRosserFailurePartialSum_succ_eq_sum_upper_of_headPow
    P nu level z R hprime]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  rw [rosserCutoffRoot_le_iff_pow_le hlevel (by positivity) (by omega)]

/-- Iwaniec's equation (4.5), with its weak root endpoint explicit. -/
theorem upperRosserFailurePartialSum_eq_sum_lower
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 0 ≤ level)
    (hcube : z ^ 3 ≤ level) :
    upperRosserFailurePartialSum P nu level z R =
      ∑ p ∈ P.filter (fun p : Nat ↦
        rosserCutoffRoot level (2 * R + 3) ≤ (p : Real) ∧
          (p : Real) < z),
        nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  rw [upperRosserFailurePartialSum_eq_sum_lower_of_headPow
    P nu level z R hprime hcube]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  rw [rosserCutoffRoot_le_iff_pow_le hlevel (by positivity) (by omega)]

end PrimesRestrictedDigits
