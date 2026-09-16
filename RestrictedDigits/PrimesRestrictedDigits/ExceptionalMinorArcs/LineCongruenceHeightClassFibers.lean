import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceHeightClasses
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite fibers of source congruence height classes

This formalizes the exact integer-box and signed-divisor fiber count in
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212. It uses the repaired sup-height minimum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Integer coefficient pairs whose sup height is at most `M`. -/
noncomputable def lineCongruencePairBox (M : Nat) :
    Finset (Prod Int Int) :=
  (Finset.Icc (-(M : Int)) (M : Int)).product
    (Finset.Icc (-(M : Int)) (M : Int))

@[simp]
theorem card_lineCongruencePairBox (M : Nat) :
    (lineCongruencePairBox M).card = (2 * M + 1) ^ 2 := by
  simp only [lineCongruencePairBox, Finset.product_eq_sprod,
    Finset.card_product]
  have hinterval :
      (Finset.Icc (-(M : Int)) (M : Int)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    have hcast :
        (M : Int) + 1 - (-(M : Int)) = ((2 * M + 1 : Nat) : Int) := by
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  rw [hinterval, pow_two]

private theorem mem_lineCongruencePairBox_of_height_le
    {M : Nat} {c : Prod Int Int}
    (hc : lineCongruencePairHeight c <= M) :
    c ∈ lineCongruencePairBox M := by
  rw [lineCongruencePairBox, Finset.product_eq_sprod,
    Finset.mem_product]
  constructor
  · rw [Finset.mem_Icc]
    have hcNat : c.1.natAbs <= M := (le_max_left _ _).trans hc
    have hcInt : abs c.1 <= (M : Int) := by
      rw [Int.abs_eq_natAbs]
      exact Int.ofNat_le.2 hcNat
    exact abs_le.mp hcInt
  · rw [Finset.mem_Icc]
    have hcNat : c.2.natAbs <= M := (le_max_right _ _).trans hc
    have hcInt : abs c.2 <= (M : Int) := by
      rw [Int.abs_eq_natAbs]
      exact Int.ofNat_le.2 hcNat
    exact abs_le.mp hcInt

/-- The selected shortest pair of a height-class member lies in its exact
integer coefficient box. -/
theorem shortestLineCongruencePair_mem_lineCongruencePairBox
    {length : Nat} {C : Finset (Fin (10 ^ length))}
    {j : Prod (Fin (length + 1)) (Fin (length + 1))}
    {a : Fin (10 ^ length)}
    (ha : a ∈ lineCongruenceHeightClass length C j) :
    shortestLineCongruencePair (10 ^ length) a.val ∈
      lineCongruencePairBox (10 ^ j.2.val) := by
  have hband := mem_lineCongruenceHeightClass_minimum_band ha
  have hminimum :
      lineCongruenceMinimum (10 ^ length) a.val <= 10 ^ j.2.val := by
    exact_mod_cast hband.2.1
  apply mem_lineCongruencePairBox_of_height_le
  rw [(shortestLineCongruencePair_spec (10 ^ length) a.val).2]
  exact hminimum

/-- Every source height class is a subfinset of its ambient set. -/
theorem lineCongruenceHeightClass_card_le_ambient
    (length : Nat) (C : Finset (Fin (10 ^ length)))
    (j : Prod (Fin (length + 1)) (Fin (length + 1))) :
    (lineCongruenceHeightClass length C j).card <= C.card := by
  apply Finset.card_le_card
  intro a ha
  exact (mem_lineCongruenceHeightClass.mp ha).1

/-- If every signed target from the coefficient box has at most `B` factor
pairs, then the class has at most the box cardinality times `B` members. -/
theorem lineCongruenceHeightClass_card_real_le_box_mul
    {length : Nat} (C : Finset (Fin (10 ^ length)))
    (j : Prod (Fin (length + 1)) (Fin (length + 1)))
    (B : Real)
    (hdivisor : forall c : Prod Int Int,
      c ∈ lineCongruencePairBox (10 ^ j.2.val) ->
      ((c.1 - c.2 * ((10 ^ length : Nat) : Int)).divisorsAntidiag.card :
          Real) <= B) :
    ((lineCongruenceHeightClass length C j).card : Real) <=
      ((lineCongruencePairBox (10 ^ j.2.val)).card : Real) * B := by
  classical
  let X : Nat := 10 ^ length
  let S := lineCongruenceHeightClass length C j
  let box := lineCongruencePairBox (10 ^ j.2.val)
  let pair : Fin X -> Prod Int Int := fun a =>
    shortestLineCongruencePair X a.val
  have hmaps :
      Set.MapsTo pair (S : Set (Fin X)) (box : Set (Prod Int Int)) := by
    intro a ha
    exact shortestLineCongruencePair_mem_lineCongruencePairBox ha
  have hfiber : forall c : Prod Int Int, c ∈ box ->
      ((S.filter fun a => pair a = c).card : Real) <= B := by
    intro c hc
    let z : Int := c.1 - c.2 * (X : Int)
    let embedding : Fin X -> Prod Int Int := fun a =>
      ((a.val : Int), z / (a.val : Int))
    have hcard :
        (S.filter fun a => pair a = c).card <=
          z.divisorsAntidiag.card := by
      apply Finset.card_le_card_of_injOn embedding
      · intro a ha
        have haData := Finset.mem_filter.mp ha
        have haClass := mem_lineCongruenceHeightClass.mp haData.1
        have htarget : Not (z = 0) := by
          dsimp only [z]
          simpa only [pair, X, haData.2] using
            shortestLineCongruencePair_target_ne_zero X a.val
              haClass.2.1 a.isLt
        have hdiv : (a.val : Int) ∣ z := by
          dsimp only [z]
          simpa only [pair, X, haData.2] using
            modulus_dvd_shortestLineCongruencePair_target X a.val
        change ((a.val : Int), z / (a.val : Int)) ∈
          z.divisorsAntidiag
        rw [Int.prodMk_mem_divisorsAntidiag htarget]
        rw [mul_comm]
        exact Int.ediv_mul_cancel hdiv
      · intro a _ b _ hab
        apply Fin.ext
        have habFirst := congrArg Prod.fst hab
        dsimp only [embedding] at habFirst
        exact_mod_cast habFirst
    calc
      ((S.filter fun a => pair a = c).card : Real) <=
          (z.divisorsAntidiag.card : Real) := by
        exact_mod_cast hcard
      _ <= B := hdivisor c hc
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (S.card : Real) =
        ∑ c ∈ box, ((S.filter fun a => pair a = c).card : Real) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun n : Nat => (n : Real)) hdecomp
    _ <= ∑ c ∈ box, B :=
      Finset.sum_le_sum fun c hc => hfiber c hc
    _ = (box.card : Real) * B := by simp

end PrimesRestrictedDigits
