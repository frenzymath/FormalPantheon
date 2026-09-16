import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry

/-!
Dimension-indexed checked rational subdivision for directed integral certificates.
Payload validation sees the exact derived leaf box; analytic bounds remain in
family-specific replay modules.
-/

open Set

namespace PrimesRestrictedDigits

variable {n : Nat} {alpha : Type*}

def RationalBox.leftChild
    (box : RationalBox n) (axis : Fin n) (cut : Rat) : RationalBox n :=
  { box with upper := Function.update box.upper axis cut }

def RationalBox.rightChild
    (box : RationalBox n) (axis : Fin n) (cut : Rat) : RationalBox n :=
  { box with lower := Function.update box.lower axis cut }

def RationalBox.cutValid
    (box : RationalBox n) (axis : Fin n) (cut : Rat) : Bool :=
  decide (box.lower axis <= cut /\ cut <= box.upper axis)

inductive RationalSubdivision (n : Nat) (alpha : Type*) where
  | retain (payload : alpha)
  | exclude (constraintIndex : Nat)
  | split (axis : Fin n) (cut : Rat)
      (left right : RationalSubdivision n alpha)
  deriving DecidableEq

def RationalSubdivision.coverValid
    (constraints : List (RationalAffineConstraint n))
    (payloadValid : RationalBox n -> alpha -> Bool)
    (box : RationalBox n) : RationalSubdivision n alpha -> Bool
  | .retain payload => box.orderedBool && payloadValid box payload
  | .exclude index => box.orderedBool &&
      match constraints[index]? with
      | none => false
      | some constraint => constraint.excludesBool box
  | .split axis cut left right =>
      box.orderedBool && box.cutValid axis cut &&
        left.coverValid constraints payloadValid (box.leftChild axis cut) &&
        right.coverValid constraints payloadValid (box.rightChild axis cut)

def RationalSubdivision.retainedLeaves
    (tree : RationalSubdivision n alpha) (box : RationalBox n) :
    List (RationalBox n × alpha) :=
  match tree with
  | .retain payload => [(box, payload)]
  | .exclude _ => []
  | .split axis cut left right =>
      left.retainedLeaves (box.leftChild axis cut) ++
        right.retainedLeaves (box.rightChild axis cut)

def RationalSubdivision.replayWeightRat
    (tree : RationalSubdivision n alpha) (box : RationalBox n)
    (payloadWeight : RationalBox n -> alpha -> Rat) : Rat :=
  match tree with
  | .retain payload => box.volumeRat * payloadWeight box payload
  | .exclude _ => 0
  | .split axis cut left right =>
      left.replayWeightRat (box.leftChild axis cut) payloadWeight +
        right.replayWeightRat (box.rightChild axis cut) payloadWeight

theorem RationalSubdivision.replayWeightRat_cast
    (tree : RationalSubdivision n alpha) (box : RationalBox n)
    (payloadWeight : RationalBox n -> alpha -> Rat) :
    (tree.replayWeightRat box payloadWeight : Real) =
      ((tree.retainedLeaves box).map fun leaf =>
        ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real)).sum := by
  induction tree generalizing box with
  | retain payload =>
      simp [RationalSubdivision.replayWeightRat,
        RationalSubdivision.retainedLeaves]
  | exclude index =>
      simp [RationalSubdivision.replayWeightRat,
        RationalSubdivision.retainedLeaves]
  | split axis cut left right ihLeft ihRight =>
      simp [RationalSubdivision.replayWeightRat,
        RationalSubdivision.retainedLeaves, ihLeft, ihRight, Rat.cast_add]

private theorem RationalBox.mem_leftChild_or_rightChild
    (box : RationalBox n) (axis : Fin n) (cut : Rat)
    {x : AffinePoint n} (hx : x ∈ box.region) :
    x ∈ (box.leftChild axis cut).region ∪
      (box.rightChild axis cut).region := by
  by_cases h : x axis <= (cut : Real)
  · left
    rw [RationalBox.region] at hx ⊢
    constructor
    · exact hx.1
    · intro i
      by_cases hi : i = axis
      · subst i
        simpa [RationalBox.leftChild] using h
      · simpa [RationalBox.leftChild, Function.update, hi] using hx.2 i
  · right
    rw [RationalBox.region] at hx ⊢
    constructor
    · intro i
      by_cases hi : i = axis
      · subst i
        simpa [RationalBox.rightChild] using (le_of_not_ge h)
      · simpa [RationalBox.rightChild, Function.update, hi] using hx.1 i
    · exact hx.2

private theorem exists_mem_retainedLeaves
    (constraints : List (RationalAffineConstraint n))
    (payloadValid : RationalBox n -> alpha -> Bool)
    (box : RationalBox n) (tree : RationalSubdivision n alpha)
    (hvalid : tree.coverValid constraints payloadValid box = true)
    {x : AffinePoint n}
    (hconstraints : ∀ constraint ∈ constraints, constraint.holds x)
    (hx : x ∈ box.region) :
    ∃ leaf ∈ tree.retainedLeaves box, x ∈ leaf.1.region := by
  induction tree generalizing box with
  | retain payload =>
      exact ⟨(box, payload), by simp [RationalSubdivision.retainedLeaves], hx⟩
  | exclude index =>
      cases hlookup : constraints[index]? with
      | none => simp [RationalSubdivision.coverValid, hlookup] at hvalid
      | some constraint =>
          have hexcludes : constraint.excludesBool box = true := by
            have hparts := hvalid
            simp only [RationalSubdivision.coverValid, hlookup,
              Bool.and_eq_true] at hparts
            exact hparts.2
          have hc : constraint ∈ constraints := List.mem_of_getElem? hlookup
          exact False.elim (constraint.not_holds_of_excludesBool box
            hexcludes hx (hconstraints constraint hc))
  | split axis cut left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [RationalSubdivision.coverValid, Bool.and_eq_true] at hparts
      rcases box.mem_leftChild_or_rightChild axis cut hx with hxLeft | hxRight
      · obtain ⟨leaf, hleaf, hmem⟩ :=
          ihLeft (box.leftChild axis cut) hparts.1.2 hxLeft
        exact ⟨leaf, List.mem_append_left _ hleaf, hmem⟩
      · obtain ⟨leaf, hleaf, hmem⟩ :=
          ihRight (box.rightChild axis cut) hparts.2 hxRight
        exact ⟨leaf, List.mem_append_right _ hleaf, hmem⟩

theorem RationalSubdivision.target_subset_retainedLeaves
    (constraints : List (RationalAffineConstraint n))
    (payloadValid : RationalBox n -> alpha -> Bool)
    (box : RationalBox n) (tree : RationalSubdivision n alpha)
    (target : Set (AffinePoint n))
    (hvalid : tree.coverValid constraints payloadValid box = true)
    (hconstraints : ∀ x ∈ target, ∀ constraint ∈ constraints,
      constraint.holds x)
    (hroot : target ⊆ box.region) :
    target ⊆ ⋃ i : Fin (tree.retainedLeaves box).length,
      ((tree.retainedLeaves box).get i).1.region := by
  intro x hx
  obtain ⟨leaf, hleaf, hxleaf⟩ := exists_mem_retainedLeaves constraints
    payloadValid box tree hvalid (hconstraints x hx) (hroot hx)
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hleaf
  refine Set.mem_iUnion.2 ⟨⟨i, hi⟩, ?_⟩
  simpa [hget] using hxleaf

theorem RationalSubdivision.valid_of_mem_retainedLeaves
    (constraints : List (RationalAffineConstraint n))
    (payloadValid : RationalBox n -> alpha -> Bool)
    (box : RationalBox n) (tree : RationalSubdivision n alpha)
    (hvalid : tree.coverValid constraints payloadValid box = true)
    {leaf : RationalBox n × alpha} (hleaf : leaf ∈ tree.retainedLeaves box) :
    leaf.1.IsOrdered /\ payloadValid leaf.1 leaf.2 = true := by
  induction tree generalizing box with
  | retain payload =>
      simp only [RationalSubdivision.retainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      simpa [RationalSubdivision.coverValid, RationalBox.orderedBool] using hvalid
  | exclude index => simp [RationalSubdivision.retainedLeaves] at hleaf
  | split axis cut left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [RationalSubdivision.coverValid, Bool.and_eq_true] at hparts
      rw [RationalSubdivision.retainedLeaves, List.mem_append] at hleaf
      exact hleaf.elim (ihLeft (box.leftChild axis cut) hparts.1.2)
        (ihRight (box.rightChild axis cut) hparts.2)

end PrimesRestrictedDigits
