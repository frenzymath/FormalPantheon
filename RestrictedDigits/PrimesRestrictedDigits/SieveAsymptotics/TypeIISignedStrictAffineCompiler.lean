import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineHalfspaces
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Sum

/-!
# Signed compilation of strict affine constraints

A finite conjunction of weak and strict affine inequalities is expanded into a signed list of
regions presented using weak inequalities only. Each strict wall contributes its weak closure
minus its equality boundary.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- An exact finite presentation mixing weak and strict affine inequalities. -/
structure TypeIIAffineMixedPresentation {d : Nat}
    (region : Set (Fin d -> Real)) where
  constraintCount : Nat
  normal : Fin constraintCount -> Fin d -> Real
  bound : Fin constraintCount -> Real
  isStrict : Fin constraintCount -> Bool
  mem_iff : forall x, x ∈ region <-> forall c,
    if isStrict c then
      typeIIAffineValue (normal c) x < bound c
    else
      typeIIAffineValue (normal c) x <= bound c

namespace TypeIIAffineMixedPresentation

/-- The finite set of constraints whose endpoint is strict. -/
def strictIndices {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) :
    Finset (Fin presentation.constraintCount) :=
  Finset.univ.filter fun c => presentation.isStrict c

@[simp] theorem mem_strictIndices_iff
    {d : Nat} {region : Set (Fin d -> Real)}
    {presentation : TypeIIAffineMixedPresentation region}
    {c : Fin presentation.constraintCount} :
    c ∈ presentation.strictIndices <-> presentation.isStrict c = true := by
  simp [strictIndices]

end TypeIIAffineMixedPresentation

/-- The weak region obtained by closing every wall and forcing the selected
strict walls to equality. -/
def typeIIAffineWeakPieceRegion
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (equalityWalls : Finset (Fin presentation.constraintCount)) :
    Set (Fin d -> Real) :=
  {x | (forall c,
      typeIIAffineValue (presentation.normal c) x <= presentation.bound c) ∧
    forall c, c ∈ equalityWalls ->
      presentation.bound c <=
        typeIIAffineValue (presentation.normal c) x}

@[simp] theorem mem_typeIIAffineWeakPieceRegion
    {d : Nat} {region : Set (Fin d -> Real)}
    {presentation : TypeIIAffineMixedPresentation region}
    {equalityWalls : Finset (Fin presentation.constraintCount)}
    {x : Fin d -> Real} :
    x ∈ typeIIAffineWeakPieceRegion presentation equalityWalls <->
      (forall c,
        typeIIAffineValue (presentation.normal c) x <= presentation.bound c) ∧
      forall c, c ∈ equalityWalls ->
        presentation.bound c <=
          typeIIAffineValue (presentation.normal c) x :=
  Iff.rfl

theorem typeIIAffineValue_neg {d : Nat}
    (normal x : Fin d -> Real) :
    typeIIAffineValue (-normal) x = -typeIIAffineValue normal x := by
  simp only [typeIIAffineValue, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

/-- The selected equality walls are appended as reversed weak inequalities.
The presentation contains no inactive padding constraints. -/
noncomputable def typeIIAffineWeakPiecePresentation
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (equalityWalls : Finset (Fin presentation.constraintCount)) :
    TypeIIAffineHalfspacePresentation
      (typeIIAffineWeakPieceRegion presentation equalityWalls) where
  constraintCount := presentation.constraintCount + equalityWalls.card
  normal := Fin.append presentation.normal fun i =>
    -presentation.normal
      ((equalityWalls.orderIsoOfFin rfl i : equalityWalls).1)
  bound := Fin.append presentation.bound fun i =>
    -presentation.bound
      ((equalityWalls.orderIsoOfFin rfl i : equalityWalls).1)
  mem_iff := by
    intro x
    rw [mem_typeIIAffineWeakPieceRegion, Fin.forall_fin_add]
    constructor
    · rintro ⟨hforward, hreverse⟩
      constructor
      · intro c
        simpa only [Fin.append_left] using hforward c
      · intro i
        let wall : equalityWalls := equalityWalls.orderIsoOfFin rfl i
        have hwall := hreverse wall.1 wall.2
        simpa only [Fin.append_right, typeIIAffineValue_neg,
          neg_le_neg_iff] using hwall
    · rintro ⟨hforward, hreverse⟩
      constructor
      · intro c
        simpa only [Fin.append_left] using hforward c
      · intro c hc
        let wall : equalityWalls := ⟨c, hc⟩
        let i : Fin equalityWalls.card :=
          (equalityWalls.orderIsoOfFin rfl).symm wall
        have hi := hreverse i
        have hwall : equalityWalls.orderIsoOfFin rfl i = wall :=
          (equalityWalls.orderIsoOfFin rfl).apply_symm_apply wall
        simpa only [Fin.append_right, typeIIAffineValue_neg,
          neg_le_neg_iff, hwall] using hi

/-- One signed weak occurrence, tagged by the subset of strict walls that it
forces to equality. The tag prevents extensionally equal regions from being
deduplicated. -/
structure TypeIIAffineSignedWeakPiece
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) where
  equalityWalls : Finset (Fin presentation.constraintCount)
  equalityWalls_subset_strict :
    equalityWalls ⊆ presentation.strictIndices

namespace TypeIIAffineSignedWeakPiece

/-- The literal inclusion-exclusion sign of one occurrence. -/
def coefficient
    {d : Nat} {region : Set (Fin d -> Real)}
    {presentation : TypeIIAffineMixedPresentation region}
    (piece : TypeIIAffineSignedWeakPiece presentation) : Int :=
  (-1 : Int) ^ piece.equalityWalls.card

/-- The weak region represented by one signed occurrence. -/
def region
    {d : Nat} {sourceRegion : Set (Fin d -> Real)}
    {presentation : TypeIIAffineMixedPresentation sourceRegion}
    (piece : TypeIIAffineSignedWeakPiece presentation) :
    Set (Fin d -> Real) :=
  typeIIAffineWeakPieceRegion presentation piece.equalityWalls

/-- The explicit finite weak presentation carried by one occurrence. -/
noncomputable def weakPresentation
    {d : Nat} {sourceRegion : Set (Fin d -> Real)}
    {presentation : TypeIIAffineMixedPresentation sourceRegion}
    (piece : TypeIIAffineSignedWeakPiece presentation) :
    TypeIIAffineHalfspacePresentation piece.region :=
  typeIIAffineWeakPiecePresentation presentation piece.equalityWalls

end TypeIIAffineSignedWeakPiece

private noncomputable def typeIIAffineSignedWeakPieceOfSubset
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (walls : {S // S ∈ presentation.strictIndices.powerset}) :
    TypeIIAffineSignedWeakPiece presentation where
  equalityWalls := walls.1
  equalityWalls_subset_strict := Finset.mem_powerset.mp walls.2

namespace TypeIIAffineMixedPresentation

/-- The multiplicity-preserving signed list, with one occurrence for every
subset of the strict constraints. -/
noncomputable def signedWeakPieces
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) :
    List (TypeIIAffineSignedWeakPiece presentation) :=
  presentation.strictIndices.powerset.attach.toList.map
    (typeIIAffineSignedWeakPieceOfSubset presentation)

/-- Every selected subset of strict walls occurs with its literal subset tag. -/
theorem exists_signedWeakPiece_of_subset
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (equalityWalls : Finset (Fin presentation.constraintCount))
    (hWalls : equalityWalls ⊆ presentation.strictIndices) :
    ∃ piece ∈ presentation.signedWeakPieces,
      piece.equalityWalls = equalityWalls := by
  classical
  let tagged : {S // S ∈ presentation.strictIndices.powerset} :=
    ⟨equalityWalls, Finset.mem_powerset.mpr hWalls⟩
  refine ⟨typeIIAffineSignedWeakPieceOfSubset presentation tagged, ?_, rfl⟩
  simp [signedWeakPieces, tagged]

end TypeIIAffineMixedPresentation

/-- The compiler retains exactly one list occurrence for every subset of the
strict-index set. -/
theorem length_signedWeakPieces
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) :
    presentation.signedWeakPieces.length =
      2 ^ presentation.strictIndices.card := by
  simp [TypeIIAffineMixedPresentation.signedWeakPieces,
    Finset.card_powerset]

private theorem sum_signedWeakPieces_eq_powerset
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (x : Fin d -> Real) :
    (presentation.signedWeakPieces.map fun piece =>
        piece.coefficient *
          Set.indicator piece.region (fun _ => (1 : Int)) x).sum =
      ∑ S ∈ presentation.strictIndices.powerset,
        (-1 : Int) ^ S.card *
          Set.indicator (typeIIAffineWeakPieceRegion presentation S)
            (fun _ => (1 : Int)) x := by
  classical
  let term : Finset (Fin presentation.constraintCount) -> Int := fun S =>
    (-1 : Int) ^ S.card *
      Set.indicator (typeIIAffineWeakPieceRegion presentation S)
        (fun _ => (1 : Int)) x
  calc
    (presentation.signedWeakPieces.map fun piece =>
        piece.coefficient *
          Set.indicator piece.region (fun _ => (1 : Int)) x).sum =
        (presentation.strictIndices.powerset.attach.toList.map
          (fun walls => term walls.1)).sum := by
            simp only [TypeIIAffineMixedPresentation.signedWeakPieces,
              List.map_map]
            rfl
    _ = ∑ walls ∈ presentation.strictIndices.powerset.attach,
          term walls.1 := Finset.sum_map_toList _ _
    _ = ∑ S ∈ presentation.strictIndices.powerset, term S :=
      Finset.sum_attach _ term
    _ = _ := rfl

/-- Exact integer-valued indicator identity for the signed compiler. -/
theorem typeIIAffineMixed_indicator_eq_signedWeakPieces
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (x : Fin d -> Real) :
    Set.indicator region (fun _ => (1 : Int)) x =
      (presentation.signedWeakPieces.map fun piece =>
        piece.coefficient *
          Set.indicator piece.region (fun _ => (1 : Int)) x).sum := by
  classical
  rw [sum_signedWeakPieces_eq_powerset]
  let J := presentation.strictIndices
  let equalities : Finset (Fin presentation.constraintCount) :=
    J.filter fun c =>
      typeIIAffineValue (presentation.normal c) x = presentation.bound c
  by_cases hforward : forall c,
      typeIIAffineValue (presentation.normal c) x <= presentation.bound c
  · have hequalitiesJ : equalities ⊆ J := Finset.filter_subset _ _
    have hpiece (S : Finset (Fin presentation.constraintCount))
        (hSJ : S ⊆ J) :
        x ∈ typeIIAffineWeakPieceRegion presentation S <->
          S ⊆ equalities := by
      constructor
      · rintro ⟨_hclosed, hreverse⟩ c hc
        have heq := le_antisymm (hforward c) (hreverse c hc)
        exact Finset.mem_filter.mpr ⟨hSJ hc, heq⟩
      · intro hSE
        refine ⟨hforward, ?_⟩
        intro c hc
        have heq := (Finset.mem_filter.mp (hSE hc)).2
        rw [heq]
    have hmixed : x ∈ region <-> equalities = ∅ := by
      rw [presentation.mem_iff]
      constructor
      · intro hx
        apply Finset.filter_eq_empty_iff.mpr
        intro c hcJ hceq
        have hstrict :=
          TypeIIAffineMixedPresentation.mem_strictIndices_iff.mp hcJ
        have hcValue := hx c
        simp [hstrict, hceq] at hcValue
      · intro hempty c
        cases hmode : presentation.isStrict c with
        | false => simpa [hmode] using hforward c
        | true =>
            have hne : typeIIAffineValue (presentation.normal c) x ≠
                presentation.bound c := by
              intro heq
              have hcJ : c ∈ J := by
                exact TypeIIAffineMixedPresentation.mem_strictIndices_iff.mpr
                  hmode
              have hcEquality : c ∈ equalities :=
                Finset.mem_filter.mpr ⟨hcJ, heq⟩
              rw [hempty] at hcEquality
              simp at hcEquality
            have hlt := lt_of_le_of_ne (hforward c) hne
            simpa [hmode] using hlt
    have hpowerset : equalities.powerset ⊆ J.powerset := by
      intro S hS
      exact Finset.mem_powerset.mpr
        ((Finset.mem_powerset.mp hS).trans hequalitiesJ)
    let term : Finset (Fin presentation.constraintCount) -> Int := fun S =>
      (-1 : Int) ^ S.card *
        Set.indicator (typeIIAffineWeakPieceRegion presentation S)
          (fun _ => (1 : Int)) x
    have hrestricted :
        (∑ S ∈ J.powerset, term S) =
          ∑ S ∈ equalities.powerset, (-1 : Int) ^ S.card := by
      symm
      calc
        (∑ S ∈ equalities.powerset, (-1 : Int) ^ S.card) =
            ∑ S ∈ equalities.powerset, term S := by
          apply Finset.sum_congr rfl
          intro S hS
          have hSE := Finset.mem_powerset.mp hS
          have hSJ := hSE.trans hequalitiesJ
          simp [term, Set.indicator_of_mem ((hpiece S hSJ).2 hSE)]
        _ = ∑ S ∈ J.powerset, term S := by
          apply Finset.sum_subset hpowerset
          intro S hSJ hSnot
          have hsubsetJ := Finset.mem_powerset.mp hSJ
          have hnotPiece :
              x ∉ typeIIAffineWeakPieceRegion presentation S := by
            intro hmem
            exact hSnot (Finset.mem_powerset.mpr
              ((hpiece S hsubsetJ).mp hmem))
          simp [term, Set.indicator_of_notMem hnotPiece]
    have halternating :
        (∑ S ∈ equalities.powerset, (-1 : Int) ^ S.card) =
          if equalities = ∅ then 1 else 0 :=
      Finset.sum_powerset_neg_one_pow_card
    rw [show
      (∑ S ∈ presentation.strictIndices.powerset,
          (-1 : Int) ^ S.card *
            Set.indicator (typeIIAffineWeakPieceRegion presentation S)
              (fun _ => (1 : Int)) x) =
        ∑ S ∈ J.powerset, term S by rfl,
      hrestricted, halternating]
    by_cases hempty : equalities = ∅
    · simp [hempty, hmixed.mpr hempty]
    · have hnotMem : x ∉ region := fun hx => hempty (hmixed.mp hx)
      simp [hempty, hnotMem]
  · have hnotRegion : x ∉ region := by
      intro hx
      have hxAll := (presentation.mem_iff x).mp hx
      apply hforward
      intro c
      cases hmode : presentation.isStrict c with
      | false => simpa [hmode] using hxAll c
      | true =>
          have hc : typeIIAffineValue (presentation.normal c) x <
              presentation.bound c := by
            simpa [hmode] using hxAll c
          exact hc.le
    rw [Set.indicator_of_notMem hnotRegion]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    rw [Set.indicator_of_notMem]
    · simp
    · intro hpiece
      exact hforward hpiece.1

/-- The same exact signed identity in the real coefficient ring used by the
later analytic estimates. -/
theorem typeIIAffineMixed_indicator_eq_signedWeakPieces_real
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (x : Fin d -> Real) :
    Set.indicator region (fun _ => (1 : Real)) x =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          Set.indicator piece.region (fun _ => (1 : Real)) x).sum := by
  classical
  have h := congrArg (fun z : Int => (z : Real))
    (typeIIAffineMixed_indicator_eq_signedWeakPieces presentation x)
  simpa [Set.indicator, List.map_map, Function.comp_def] using h

end

end PrimesRestrictedDigits
