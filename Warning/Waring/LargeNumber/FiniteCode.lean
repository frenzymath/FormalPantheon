import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Order

/-!
# Finite-coordinate sum codes

This file extends the separated pair-code argument to the heterogeneous finite
tuples used in Chen's English Lemma 11 / Chinese Lemma 12
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

universe u

/-- Sum of all coordinate codes in a heterogeneous finite tuple. -/
def finCode {n : Nat} {A : Fin n → Type u}
    (digit : ∀ i, A i → Nat) (x : ∀ i, A i) : Nat :=
  ∑ i, digit i (x i)

/-- The part of a finite tuple code strictly after a given coordinate. -/
def finCodeSuffix {n : Nat} {A : Fin n → Type u}
    (digit : ∀ i, A i → Nat) (i : Fin n) (x : ∀ i, A i) : Nat :=
  ∑ j ∈ Finset.Ioi i, digit j (x j)

private theorem finCode_split {n : Nat} {A : Fin n → Type u}
    (digit : ∀ i, A i → Nat) (i : Fin n) (x : ∀ i, A i) :
    finCode digit x =
      (∑ j ∈ Finset.Iio i, digit j (x j)) +
        digit i (x i) + finCodeSuffix digit i x := by
  let f : Fin n → Nat := fun j ↦ digit j (x j)
  have hDisjoint : Disjoint (Finset.Iio i) (Finset.Ici i) := by
    rw [Finset.disjoint_left]
    intro j hjlt hjge
    exact (not_lt_of_ge (Finset.mem_Ici.mp hjge)) (Finset.mem_Iio.mp hjlt)
  have hUnion : Finset.Iio i ∪ Finset.Ici i = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici,
      Finset.mem_univ, iff_true]
    exact lt_or_ge j i
  calc
    finCode digit x = ∑ j, f j := rfl
    _ = (∑ j ∈ Finset.Iio i, f j) + ∑ j ∈ Finset.Ici i, f j := by
      rw [← Finset.sum_union hDisjoint, hUnion]
    _ = (∑ j ∈ Finset.Iio i, f j) +
        (f i + ∑ j ∈ Finset.Ioi i, f j) := by
      rw [Finset.add_sum_Ioi_eq_sum_Ici]
    _ = (∑ j ∈ Finset.Iio i, digit j (x j)) +
        digit i (x i) + finCodeSuffix digit i x := by
      simp only [f, finCodeSuffix, add_assoc]

/-- If two tuples agree before `i` and their `i`-th digits are ordered,
suffix interval separation makes their complete codes strictly ordered. -/
theorem finCode_lt_of_first_lt {n : Nat} {A : Fin n → Type u}
    {digit : ∀ i, A i → Nat} {tailLower tailUpper : Fin n → Nat}
    {x y : ∀ i, A i} {i : Fin n}
    (hBefore : ∀ j, j < i → x j = y j)
    (hTailX : finCodeSuffix digit i x < tailUpper i)
    (hTailY : tailLower i ≤ finCodeSuffix digit i y)
    (hSeparate : digit i (x i) + tailUpper i ≤
      digit i (y i) + tailLower i) :
    finCode digit x < finCode digit y := by
  have hPrefix :
      (∑ j ∈ Finset.Iio i, digit j (x j)) =
        ∑ j ∈ Finset.Iio i, digit j (y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hBefore j (Finset.mem_Iio.mp hj)]
  rw [finCode_split digit i x, finCode_split digit i y, hPrefix]
  have hRest : digit i (x i) + finCodeSuffix digit i x <
      digit i (y i) + finCodeSuffix digit i y := calc
    digit i (x i) + finCodeSuffix digit i x <
        digit i (x i) + tailUpper i := Nat.add_lt_add_left hTailX _
    _ ≤ digit i (y i) + tailLower i := hSeparate
    _ ≤ digit i (y i) + finCodeSuffix digit i y :=
      Nat.add_le_add_left hTailY _
  omega

/-- A finite sum code is injective if every coordinate code is injective and
each possible first differing coordinate separates the prescribed suffix
intervals. -/
theorem finCode_injective {n : Nat} {A : Fin n → Type u}
    {digit : ∀ i, A i → Nat} {tailLower tailUpper : Fin n → Nat}
    (hDigit : ∀ i, Function.Injective (digit i))
    (hTail : ∀ i x, finCodeSuffix digit i x ∈
      Finset.Ico (tailLower i) (tailUpper i))
    (hSeparate : ∀ i (a₁ a₂ : A i), digit i a₁ < digit i a₂ →
      digit i a₁ + tailUpper i ≤ digit i a₂ + tailLower i) :
    Function.Injective (finCode digit) := by
  intro x y hCode
  by_contra hxy
  have hNonempty : {i | x i ≠ y i}.Nonempty := Function.ne_iff.mp hxy
  let wf : WellFounded ((· < ·) : Fin n → Fin n → Prop) := IsWellFounded.wf
  let i := wf.min {i | x i ≠ y i} hNonempty
  have hi : x i ≠ y i := wf.min_mem _ hNonempty
  have hBefore : ∀ j, j < i → x j = y j := by
    intro j hj
    by_contra hne
    exact wf.not_lt_min _ hne hj
  have hDigitNe : digit i (x i) ≠ digit i (y i) :=
    fun h ↦ hi (hDigit i h)
  rcases lt_or_gt_of_ne hDigitNe with hlt | hgt
  · have hltCode : finCode digit x < finCode digit y :=
      finCode_lt_of_first_lt hBefore (Finset.mem_Ico.mp (hTail i x)).2
        (Finset.mem_Ico.mp (hTail i y)).1
        (hSeparate i (x i) (y i) hlt)
    exact hltCode.ne hCode
  · have hltCode : finCode digit y < finCode digit x :=
      finCode_lt_of_first_lt (fun j hj ↦ (hBefore j hj).symm)
        (Finset.mem_Ico.mp (hTail i y)).2
        (Finset.mem_Ico.mp (hTail i x)).1
        (hSeparate i (y i) (x i) hgt)
    exact hltCode.ne hCode.symm

/-- Closed coordinate bounds imply the suffix hypotheses of
`finCode_injective` when the corresponding closed suffix intervals are
strictly separated. -/
theorem finCode_injective_of_closed_bounds {n : Nat} {A : Fin n → Type u}
    {digit : ∀ i, A i → Nat} {lower upper : Fin n → Nat}
    (hDigit : ∀ i, Function.Injective (digit i))
    (hLower : ∀ i a, lower i ≤ digit i a)
    (hUpper : ∀ i a, digit i a ≤ upper i)
    (hSeparate : ∀ i (a₁ a₂ : A i), digit i a₁ < digit i a₂ →
      digit i a₁ + (∑ j ∈ Finset.Ioi i, upper j) <
        digit i a₂ + ∑ j ∈ Finset.Ioi i, lower j) :
    Function.Injective (finCode digit) := by
  let tailLower : Fin n → Nat := fun i ↦ ∑ j ∈ Finset.Ioi i, lower j
  let tailUpper : Fin n → Nat := fun i ↦ (∑ j ∈ Finset.Ioi i, upper j) + 1
  apply finCode_injective hDigit (tailLower := tailLower)
    (tailUpper := tailUpper)
  · intro i x
    rw [Finset.mem_Ico]
    constructor
    · exact Finset.sum_le_sum fun j _ ↦ hLower j (x j)
    · apply Nat.lt_succ_of_le
      exact Finset.sum_le_sum fun j _ ↦ hUpper j (x j)
  · intro i a₁ a₂ hlt
    dsimp only [tailLower, tailUpper]
    have := hSeparate i a₁ a₂ hlt
    omega

/-- Coordinatewise closed bounds give the corresponding closed range for a
finite sum code. -/
theorem finCode_mem_Icc {n : Nat} {A : Fin n → Type u}
    {digit : ∀ i, A i → Nat} {lower upper : Fin n → Nat}
    (hLower : ∀ i a, lower i ≤ digit i a)
    (hUpper : ∀ i a, digit i a ≤ upper i) (x : ∀ i, A i) :
    finCode digit x ∈ Finset.Icc (∑ i, lower i) (∑ i, upper i) := by
  rw [Finset.mem_Icc]
  exact ⟨Finset.sum_le_sum fun i _ ↦ hLower i (x i),
    Finset.sum_le_sum fun i _ ↦ hUpper i (x i)⟩

/-- The image of an injective finite sum code has the product cardinality of
the independent coordinate types. -/
theorem card_finCode_image {n : Nat} {A : Fin n → Type u}
    [∀ i, Fintype (A i)] (digit : ∀ i, A i → Nat)
    (hCode : Function.Injective (finCode digit)) :
    (Finset.univ.image (finCode digit)).card =
      ∏ i, Fintype.card (A i) := by
  rw [Finset.card_image_of_injective _ hCode, Finset.card_univ,
    Fintype.card_pi]

end Waring.LargeNumber
