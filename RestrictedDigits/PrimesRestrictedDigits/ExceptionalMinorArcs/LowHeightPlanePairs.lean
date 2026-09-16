import PrimesRestrictedDigits.ExceptionalMinorArcs.LineLowHeightPlane
import Mathlib.Tactic.Ring

/-!
# The finite low-height plane-pair carrier

This is the exact ordered carrier in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2,
p. 210. It retains the source's closed real coefficient box and nonzero
integer quadruple.
-/

namespace PrimesRestrictedDigits

/-- An ordered pair admits a nontrivial integral relation of height at most
`V` with the source coefficient order `(a1,a2,X,1)`. -/
def IsLowHeightPlanePair {X : Nat}
    (V : Real) (a1 a2 : Fin X) : Prop :=
  exists (v : Fin 3 -> Int) (v4 : Int),
    And (Or (Not (v = 0)) (Not (v4 = 0)))
      (And (forall i, abs ((v i : Int) : Real) <= V)
        (And (abs ((v4 : Int) : Real) <= V)
          (intVectorDot v (lineCoefficientVector a1 a2) + v4 = 0)))

/-- The ordered pairs from `C` satisfying a low-height plane relation. -/
noncomputable def lowHeightPlanePairs {X : Nat}
    (C : Finset (Fin X)) (V : Real) : Finset (Prod (Fin X) (Fin X)) := by
  classical
  exact (C.product C).filter fun pair =>
    IsLowHeightPlanePair V pair.1 pair.2

@[simp]
theorem mem_lowHeightPlanePairs {X : Nat} {C : Finset (Fin X)}
    {V : Real} {a1 a2 : Fin X} :
    (a1, a2) ∈ lowHeightPlanePairs C V <->
      And (a1 ∈ C) (And (a2 ∈ C) (IsLowHeightPlanePair V a1 a2)) := by
  classical
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hproduct := Finset.mem_product.mp h'.1
    exact ⟨hproduct.1, hproduct.2, h'.2⟩
  · rintro ⟨ha1, ha2, hrelation⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha1, ha2⟩,
      hrelation⟩

/-- Below height one, an integer quadruple in the closed coefficient box must
be zero, so no source relation is admissible. -/
theorem not_isLowHeightPlanePair_of_lt_one
    {X : Nat} {V : Real} (hV : V < 1) (a1 a2 : Fin X) :
    Not (IsLowHeightPlanePair V a1 a2) := by
  rintro ⟨v, v4, hnonzero, hv, hv4, _hrelation⟩
  have hvzero : v = 0 := by
    funext i
    have hi : abs ((v i : Int) : Real) < 1 := (hv i).trans_lt hV
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt,
      Int.abs_lt_one_iff] at hi
    exact hi
  have hv4zero : v4 = 0 := by
    have hi : abs ((v4 : Int) : Real) < 1 := hv4.trans_lt hV
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt,
      Int.abs_lt_one_iff] at hi
    exact hi
  exact hnonzero.elim (fun h => h hvzero) (fun h => h hv4zero)

/-- The finite carrier is empty whenever the real height is below one. -/
theorem lowHeightPlanePairs_eq_empty_of_lt_one
    {X : Nat} (C : Finset (Fin X)) {V : Real} (hV : V < 1) :
    lowHeightPlanePairs C V = Finset.empty := by
  classical
  exact Finset.eq_empty_iff_forall_notMem.mpr fun pair hpair =>
    not_isLowHeightPlanePair_of_lt_one hV pair.1 pair.2
      (Finset.mem_filter.mp hpair).2

/-- Filtering the ordered square never increases its cardinality. -/
theorem card_lowHeightPlanePairs_le_sq
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    (lowHeightPlanePairs C V).card <= C.card ^ 2 := by
  classical
  calc
    (lowHeightPlanePairs C V).card <= (C.product C).card := by
      exact Finset.card_filter_le _ _
    _ = C.card * C.card := Finset.card_product C C
    _ = C.card ^ 2 := by ring

end PrimesRestrictedDigits
