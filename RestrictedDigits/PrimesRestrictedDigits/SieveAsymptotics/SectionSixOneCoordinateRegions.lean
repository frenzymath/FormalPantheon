import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler

/-!
# One-coordinate regions for the first Section 6 residual

These are the exact weak cumulative and strict lower regions used to remove the first
Proposition 6.1/6.2 residual from Maynard's Eq. (6.5).

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140.
-/

namespace PrimesRestrictedDigits

/-- The cumulative weak one-coordinate region `x 0 <= upper`. -/
def sectionSixOneCoordinateUpperRegion (upper : Real) :
    Set (Fin 1 -> Real) :=
  {x | x 0 <= upper}

/-- The strict-left, weak-right one-coordinate interval `(lower, upper]`. -/
def sectionSixOneCoordinateIocRegion (lower upper : Real) :
    Set (Fin 1 -> Real) :=
  {x | lower < x 0 ∧ x 0 <= upper}

/-- The strict one-coordinate lower region `lower < x 0`. -/
def sectionSixOneCoordinateStrictLowerRegion (lower : Real) :
    Set (Fin 1 -> Real) :=
  {x | lower < x 0}

/-- The empty list of weak affine constraints presents the full
zero-dimensional space. -/
def sectionSixZeroDimensionalUnivPresentation :
    TypeIIAffineHalfspacePresentation
      (Set.univ : Set (Fin 0 -> Real)) where
  constraintCount := 0
  normal := Fin.elim0
  bound := Fin.elim0
  mem_iff := by simp

/-- One weak affine wall presents a cumulative upper region. -/
def sectionSixOneCoordinateUpperPresentation (upper : Real) :
    TypeIIAffineHalfspacePresentation
      (sectionSixOneCoordinateUpperRegion upper) where
  constraintCount := 1
  normal := fun _ _ => 1
  bound := fun _ => upper
  mem_iff := by
    intro x
    simp [sectionSixOneCoordinateUpperRegion, typeIIAffineValue]

/-- The inequality `lower < x 0` is the strict affine wall
`-x 0 < -lower`. -/
def sectionSixOneCoordinateStrictLowerPresentation (lower : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixOneCoordinateStrictLowerRegion lower) where
  constraintCount := 1
  normal := fun _ _ => -1
  bound := fun _ => -lower
  isStrict := fun _ => true
  mem_iff := by
    intro x
    change lower < x 0 <->
      forall c : Fin 1,
        typeIIAffineValue (fun _ : Fin 1 => -1) x < -lower
    simp [typeIIAffineValue]

/-- A strict-left interval is exactly a difference of two cumulative weak
regions. Equality at the lower endpoint is removed by the difference. -/
theorem sectionSixOneCoordinateIocRegion_eq_sdiff (lower upper : Real) :
    sectionSixOneCoordinateIocRegion lower upper =
      sectionSixOneCoordinateUpperRegion upper \
        sectionSixOneCoordinateUpperRegion lower := by
  ext x
  simp [sectionSixOneCoordinateIocRegion,
    sectionSixOneCoordinateUpperRegion, and_comm]

end PrimesRestrictedDigits
