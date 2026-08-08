import Waring.Analytic.ChenTenGammaLower
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Chen's fifteen-variable cumulative volume

This module formalizes the unit-cell comparison behind Chen's cumulative
count `K15(X)`: the signed cells are disjoint, their union is contained in
the fifth-power ball, and the ball volume gives the cubic upper bound.
-/

namespace Waring.Analytic

open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

open BoxIntegral
open BoxIntegral.unitPartition

noncomputable section

/-- The integer box index determined coordinatewise by a magnitude and sign. -/
def cellIndex (a : Fin 15 → Nat) (sgn : Fin 15 → Bool) : Fin 15 → Int :=
  fun i => if sgn i then (a i : Int) else - (a i : Int) - 1

/-- The unit-partition box associated with a magnitude tuple and sign tuple. -/
def signedCell (a : Fin 15 → Nat) (sgn : Fin 15 → Bool) : Set (Fin 15 → Real) :=
  (BoxIntegral.unitPartition.box 1 (cellIndex a sgn) : Set (Fin 15 → Real))

/-- Every signed cell has Lebesgue volume one. -/
theorem signedCell_volume (a : Fin 15 → Nat) (sgn : Fin 15 → Bool) :
    volume (signedCell a sgn) = 1 := by
  dsimp [signedCell]
  convert BoxIntegral.unitPartition.volume_box (n := 1)
    (ν := cellIndex a sgn) using 1
  norm_num

/-- Signed cells with different integer box indices are disjoint. -/
theorem signedCell_disjoint_of_index_ne
    {a b : Fin 15 → Nat} {s t : Fin 15 → Bool}
    (h : cellIndex a s ≠ cellIndex b t) :
    Disjoint (signedCell a s) (signedCell b t) := by
  exact (BoxIntegral.unitPartition.disjoint (n := 1)).mp h

/-- The cumulative number of positive fifteen-tuples with fifth-power sum at
most `X`; a `Fin X` coordinate stores the positive value minus one. -/
def K15 (X : Nat) : Nat :=
  ((Finset.univ : Finset (Fin 15 → Fin X)).filter
    (fun a => ∑ i, ((a i).val + 1) ^ 5 ≤ X)).card

/-- The predicate that a positive fifteen-tuple has fifth-power sum at most `X`. -/
def valid15 (X : Nat) (a : Fin 15 → Fin X) : Prop :=
  ∑ i, ((a i).val + 1) ^ 5 ≤ X

/-- The finite set of positive fifteen-tuples valid at cumulative bound `X`. -/
def validTuples15 (X : Nat) : Finset (Fin 15 → Fin X) :=
  by classical exact Finset.univ.filter (valid15 X)

/-- Valid magnitude tuples paired with all coordinatewise sign choices. -/
def signedTuples15 (X : Nat) :
    Finset ((Fin 15 → Fin X) × (Fin 15 → Bool)) :=
  validTuples15 X ×ˢ Finset.univ

/-- Forget the coordinate bounds of a tuple valued in `Fin X`. -/
def finTupleVal {X : Nat} (a : Fin 15 → Fin X) : Fin 15 → Nat :=
  fun i => (a i).val

/-- The union of all unit cells attached to valid tuples and sign vectors. -/
def signedUnion15 (X : Nat) : Set (Fin 15 → Real) :=
  ⋃ p ∈ signedTuples15 X, signedCell (finTupleVal p.1) p.2

/-- Magnitudes and signs are uniquely determined by their integer box index. -/
theorem cellIndex_injective :
    Function.Injective
      (fun p : (Fin 15 → Nat) × (Fin 15 → Bool) => cellIndex p.1 p.2) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  change cellIndex a s = cellIndex b t at h
  have hab : a = b := by
    funext i
    have hi := congrFun h i
    by_cases hs : s i
    · by_cases ht : t i
      · simp [cellIndex, hs, ht] at hi
        exact_mod_cast hi
      · simp [cellIndex, hs, ht] at hi
        have ha : (0 : Int) ≤ (a i : Int) := by omega
        have hb : (0 : Int) ≤ (b i : Int) := by omega
        omega
    · by_cases ht : t i
      · simp [cellIndex, hs, ht] at hi
        have ha : (0 : Int) ≤ (a i : Int) := by omega
        have hb : (0 : Int) ≤ (b i : Int) := by omega
        omega
      · simp [cellIndex, hs, ht] at hi
        exact_mod_cast hi
  subst b
  have hst : s = t := by
    funext i
    by_cases hs : s i
    · by_cases ht : t i
      · simp [hs, ht]
      · have hi := congrFun h i
        simp [cellIndex, hs, ht] at hi
        omega
    · by_cases ht : t i
      · have hi := congrFun h i
        simp [cellIndex, hs, ht] at hi
        omega
      · simp [hs, ht]
  exact Prod.ext rfl hst

/-- Distinct magnitude-sign pairs determine disjoint signed cells. -/
theorem signedCell_disjoint_of_pair_ne
    {a b : Fin 15 → Nat} {s t : Fin 15 → Bool}
    (h : (a, s) ≠ (b, t)) :
    Disjoint (signedCell a s) (signedCell b t) := by
  apply signedCell_disjoint_of_index_ne
  intro hi
  apply h
  exact cellIndex_injective hi

/-- Forgetting the `Fin X` bounds is injective. -/
theorem finTupleVal_injective {X : Nat} : Function.Injective (@finTupleVal X) := by
  intro a b h
  funext i
  exact Fin.ext (congrFun h i)

/-- Forgetting bounds in a signed tuple is injective. -/
theorem signedTupleVal_injective {X : Nat} :
    Function.Injective
      (fun p : (Fin 15 → Fin X) × (Fin 15 → Bool) => (finTupleVal p.1, p.2)) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  apply Prod.ext
  · apply finTupleVal_injective
    exact congrArg Prod.fst h
  · simpa using congrArg Prod.snd h

/-- The cells indexed by valid signed tuples are pairwise disjoint. -/
theorem signedCells_pairwiseDisjoint (X : Nat) :
    (↑(signedTuples15 X) : Set ((Fin 15 → Fin X) × (Fin 15 → Bool))).PairwiseDisjoint
      (fun p => signedCell (finTupleVal p.1) p.2) := by
  intro p _ q _ hpq
  apply signedCell_disjoint_of_pair_ne
  intro h
  apply hpq
  exact signedTupleVal_injective h

/-- Every signed cell is measurable. -/
theorem signedCell_measurable (a : Fin 15 → Nat) (s : Fin 15 → Bool) :
    MeasurableSet (signedCell a s) := by
  exact (BoxIntegral.unitPartition.box 1 (cellIndex a s)).measurableSet_coe

/-- `K15` is the cardinality of the finite set of valid tuples. -/
theorem K15_eq_validTuples15_card (X : Nat) : K15 X = (validTuples15 X).card := by
  simp [K15, validTuples15, valid15]

/-- Adding all fifteen sign choices multiplies the valid-tuple count by `2 ^ 15`. -/
theorem card_signedTuples15 (X : Nat) :
    (signedTuples15 X).card = 2 ^ 15 * K15 X := by
  rw [signedTuples15, Finset.card_product, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    K15_eq_validTuples15_card]
  omega

/-- The signed-cell union has volume `2 ^ 15 * K15 X`. -/
theorem volume_signedUnion15 (X : Nat) :
    volume (signedUnion15 X) = (2 ^ 15 * K15 X : Nat) := by
  rw [signedUnion15,
    MeasureTheory.measure_biUnion_finset (signedCells_pairwiseDisjoint X)]
  · simp_rw [signedCell_volume]
    simp [card_signedTuples15]
  · intro p hp
    exact signedCell_measurable _ _

/-- The fifteen-dimensional `ell^5` ball used in the volume comparison. -/
def ball15 (r : Real) : Set (Fin 15 → Real) :=
  {x | (∑ i, |x i| ^ (5 : Real)) ^ (1 / (5 : Real)) ≤ r}

/-- A coordinate in a signed cell has magnitude at most its base plus one. -/
theorem abs_mem_signedCell_le_base
    {a : Fin 15 → Nat} {s : Fin 15 → Bool} {x : Fin 15 → Real}
    (hx : x ∈ signedCell a s) (i : Fin 15) :
    |x i| ≤ a i + 1 := by
  have hi := (BoxIntegral.unitPartition.mem_box_iff (n := 1)
    (ν := cellIndex a s)).mp hx i
  simp only [Nat.cast_one] at hi
  by_cases hs : s i
  · simp [cellIndex, hs] at hi
    have ha : (0 : Real) ≤ a i := by positivity
    rw [abs_of_nonneg (ha.trans hi.1.le)]
    exact hi.2
  · simp [cellIndex, hs] at hi
    have ha : (0 : Real) ≤ a i := by positivity
    rw [abs_of_nonpos (by linarith [hi.2])]
    linarith [hi.1]

/-- A cell belonging to a valid tuple lies within the fifth-power sum bound. -/
theorem signedCell_sum_rpow_le
    {X : Nat} {a : Fin 15 → Fin X} {s : Fin 15 → Bool}
    {x : Fin 15 → Real} (ha : valid15 X a) (hx : x ∈ signedCell (finTupleVal a) s) :
    ∑ i, Real.rpow |x i| (5 : Real) ≤ (X : Real) := by
  have hcoord : ∀ i, Real.rpow |x i| (5 : Real) ≤
      Real.rpow (((a i).val + 1 : Nat) : Real) (5 : Real) := by
    intro i
    have hi := abs_mem_signedCell_le_base hx i
    simp [finTupleVal] at hi
    have hi' : |x i| ≤ (((a i).val + 1 : Nat) : Real) := by
      exact_mod_cast hi
    exact Real.rpow_le_rpow (abs_nonneg _) hi' (by positivity)
  calc
    ∑ i, Real.rpow |x i| (5 : Real) ≤
        ∑ i, Real.rpow (((a i).val + 1 : Nat) : Real) (5 : Real) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ (X : Real) := by
      simpa [Real.rpow_natCast] using (show
        (∑ i, (((a i).val + 1 : Nat) : Real) ^ (5 : Nat)) ≤ (X : Real) by
          exact_mod_cast ha)

/-- The union of valid signed cells is contained in the corresponding fifth-power ball. -/
theorem signedUnion15_subset_ball15 (X : Nat) :
    signedUnion15 X ⊆ ball15 ((X : Real) ^ (1 / (5 : Real))) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hp, hx⟩
  have hp' : p.1 ∈ validTuples15 X := by
    simpa [signedTuples15] using (Finset.mem_product.mp hp).1
  have ha : valid15 X p.1 := (Finset.mem_filter.mp hp').2
  have hsum := signedCell_sum_rpow_le ha hx
  change (∑ i, Real.rpow |x i| (5 : Real)) ^ (1 / (5 : Real)) ≤
    (X : Real) ^ (1 / (5 : Real))
  have hsum_nonneg : 0 ≤ ∑ i, Real.rpow |x i| (5 : Real) := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  exact Real.rpow_le_rpow hsum_nonneg hsum (by norm_num)

/-- The fifteenth power of the fifth-root radius is `X ^ 3`. -/
theorem rpow_fifth_radius_pow_fifteen (X : Nat) :
    ((X : Real) ^ (1 / (5 : Real))) ^ (15 : Nat) = (X : Real) ^ (3 : Nat) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- The real volume of the fifteen-dimensional fifth-power ball. -/
theorem volume_ball15_toReal (r : Real) (hr : 0 ≤ r) :
    (volume (ball15 r)).toReal =
      (2 : Real) ^ 15 * chenTenT15 * r ^ 15 := by
  rw [ball15, MeasureTheory.volume_sum_rpow_le (ι := Fin 15) (p := (5 : ℝ))
    (by norm_num)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal]
  · norm_num [Fintype.card_fin]
    dsimp [chenTenT15]
    rw [show Real.Gamma 4 = 6 by norm_num]
    ring
  · positivity

/-- Volume monotonicity gives the cubic upper bound for `K15`. -/
theorem K15_upper (X : Nat) :
    (K15 X : Real) * 2 ^ 15 ≤ chenTenT15 * (X : Real) ^ 3 * 2 ^ 15 := by
  have hmono : volume (signedUnion15 X) ≤
      volume (ball15 ((X : Real) ^ (1 / (5 : Real)))) :=
    measure_mono (signedUnion15_subset_ball15 X)
  have hball_ne : volume (ball15 ((X : Real) ^ (1 / (5 : Real)))) ≠ ∞ := by
    rw [ball15, MeasureTheory.volume_sum_rpow_le (ι := Fin 15) (p := (5 : Real))
      (by norm_num)]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hmonoReal := ENNReal.toReal_mono hball_ne hmono
  rw [volume_signedUnion15 X, volume_ball15_toReal] at hmonoReal
  · rw [rpow_fifth_radius_pow_fifteen] at hmonoReal
    convert hmonoReal using 1 <;>
      simp [chenTenT15] <;> ring
  · positivity

end

end Waring.Analytic
