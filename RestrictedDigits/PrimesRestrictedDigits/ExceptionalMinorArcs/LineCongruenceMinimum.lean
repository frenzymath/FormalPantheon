import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# The source congruence minimum

This implements the repaired shortest-pair arithmetic from
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212. The minimum ranges over
nonzero integer pairs and therefore allows either coordinate to vanish.
-/

namespace PrimesRestrictedDigits

/-- The integer sup height of a source congruence pair. -/
def lineCongruencePairHeight (c : Prod Int Int) : Nat :=
  max c.1.natAbs c.2.natAbs

/-- A nonzero source pair satisfying `c1 = c2 * X (mod a)`. -/
def IsLineCongruencePair
    (X a : Nat) (c : Prod Int Int) : Prop :=
  And (Not (c = 0))
    (Int.ModEq (a : Int) c.1 (c.2 * (X : Int)))

private theorem exists_lineCongruencePairHeight (X a : Nat) :
    exists h : Nat, exists c : Prod Int Int,
      And (IsLineCongruencePair X a c)
        (lineCongruencePairHeight c = h) := by
  refine ⟨max X 1, ((X : Int), 1), ?_, ?_⟩
  · constructor
    · intro hzero
      have hsnd := congrArg Prod.snd hzero
      norm_num at hsnd
    · simp
  · simp [lineCongruencePairHeight]

/-- The least sup height of a nonzero source congruence pair. This is total;
the source range later supplies a positive modulus. -/
noncomputable def lineCongruenceMinimum (X a : Nat) : Nat := by
  classical
  exact Nat.find (exists_lineCongruencePairHeight X a)

theorem exists_lineCongruencePair_height_eq_minimum (X a : Nat) :
    exists c : Prod Int Int, And (IsLineCongruencePair X a c)
      (lineCongruencePairHeight c = lineCongruenceMinimum X a) := by
  classical
  exact Nat.find_spec (exists_lineCongruencePairHeight X a)

/-- A fixed pair attaining the source congruence minimum. -/
noncomputable def shortestLineCongruencePair
    (X a : Nat) : Prod Int Int :=
  Classical.choose (exists_lineCongruencePair_height_eq_minimum X a)

theorem shortestLineCongruencePair_spec (X a : Nat) :
    And (IsLineCongruencePair X a (shortestLineCongruencePair X a))
      (lineCongruencePairHeight (shortestLineCongruencePair X a) =
        lineCongruenceMinimum X a) :=
  Classical.choose_spec (exists_lineCongruencePair_height_eq_minimum X a)

theorem lineCongruenceMinimum_le_height
    (X a : Nat) (c : Prod Int Int)
    (hc : IsLineCongruencePair X a c) :
    lineCongruenceMinimum X a <= lineCongruencePairHeight c := by
  classical
  exact Nat.find_min' (exists_lineCongruencePairHeight X a) ⟨c, hc, rfl⟩

theorem lineCongruenceMinimum_pos (X a : Nat) :
    0 < lineCongruenceMinimum X a := by
  obtain ⟨c, hc, hheight⟩ :=
    exists_lineCongruencePair_height_eq_minimum X a
  rw [← hheight]
  exact Nat.pos_of_ne_zero fun hzero => hc.1 (by
    apply Prod.ext
    · apply Int.natAbs_eq_zero.mp
      have : c.1.natAbs <= 0 := by
        calc
          c.1.natAbs <= lineCongruencePairHeight c := le_max_left _ _
          _ <= 0 := hzero.le
      omega
    · apply Int.natAbs_eq_zero.mp
      have : c.2.natAbs <= 0 := by
        calc
          c.2.natAbs <= lineCongruencePairHeight c := le_max_right _ _
          _ <= 0 := hzero.le
      omega)

/-- The axis witness `(a,0)` bounds the minimum by every positive modulus. -/
theorem lineCongruenceMinimum_le_modulus
    (X a : Nat) (ha : 0 < a) :
    lineCongruenceMinimum X a <= a := by
  calc
    lineCongruenceMinimum X a <=
        lineCongruencePairHeight ((a : Int), 0) := by
      apply lineCongruenceMinimum_le_height
      constructor
      · intro hzero
        have hfst := congrArg Prod.fst hzero
        norm_num at hfst
        exact ha.ne' hfst
      · simp [Int.modEq_iff_dvd]
    _ = a := by simp [lineCongruencePairHeight]

theorem lineCongruenceMinimum_lt_scale
    (X a : Nat) (ha : 0 < a) (haX : a < X) :
    lineCongruenceMinimum X a < X :=
  (lineCongruenceMinimum_le_modulus X a ha).trans_lt haX

/-- A nonzero source pair of height below `X` cannot satisfy the corresponding
integer equality, so its divisor target is nonzero. -/
theorem lineCongruencePair_target_ne_zero
    (X a : Nat) (c : Prod Int Int)
    (hc : IsLineCongruencePair X a c)
    (hheight : lineCongruencePairHeight c < X) :
    Not (c.1 - c.2 * (X : Int) = 0) := by
  intro htarget
  have hc1 : c.1 = c.2 * (X : Int) := sub_eq_zero.mp htarget
  by_cases hc2 : c.2 = 0
  · apply hc.1
    apply Prod.ext
    · simpa [hc2] using hc1
    · exact hc2
  · have hc1lt : c.1.natAbs < X :=
      (le_max_left _ _).trans_lt hheight
    have hc2One : 1 <= c.2.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc2)
    have hXle : X <= c.2.natAbs * X := by
      simpa only [one_mul] using Nat.mul_le_mul_right X hc2One
    have habs : c.1.natAbs = c.2.natAbs * X := by
      rw [hc1, Int.natAbs_mul]
      simp
    exact (not_lt_of_ge (habs ▸ hXle)) hc1lt

theorem shortestLineCongruencePair_target_ne_zero
    (X a : Nat) (ha : 0 < a) (haX : a < X) :
    Not ((shortestLineCongruencePair X a).1 -
        (shortestLineCongruencePair X a).2 * (X : Int) = 0) := by
  exact lineCongruencePair_target_ne_zero X a
    (shortestLineCongruencePair X a)
    (shortestLineCongruencePair_spec X a).1
    ((shortestLineCongruencePair_spec X a).2.trans_lt
      (lineCongruenceMinimum_lt_scale X a ha haX))

theorem modulus_dvd_shortestLineCongruencePair_target
    (X a : Nat) :
    (a : Int) ∣
      (shortestLineCongruencePair X a).1 -
        (shortestLineCongruencePair X a).2 * (X : Int) := by
  have hdiv := (shortestLineCongruencePair_spec X a).1.2.dvd
  have hneg :
      -((shortestLineCongruencePair X a).1 -
        (shortestLineCongruencePair X a).2 * (X : Int)) =
      (shortestLineCongruencePair X a).2 * (X : Int) -
        (shortestLineCongruencePair X a).1 := by ring
  exact Int.dvd_neg.mp (hneg ▸ hdiv)

end PrimesRestrictedDigits
