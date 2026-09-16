import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionGeometry

/-!
# Finite affine presentations of Type II source regions

This file records the finite weak inequalities used to present a source region and pulls them
back through canonical sum-one completion. It contains no boundary-slab or grid-counting
argument.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Evaluation of a homogeneous affine normal at one finite real tuple. -/
def typeIIAffineValue {d : Nat} (normal x : Fin d -> Real) : Real :=
  ∑ i, normal i * x i

/-- An exact finite presentation by weak affine halfspace inequalities. -/
structure TypeIIAffineHalfspacePresentation {d : Nat}
    (region : Set (Fin d -> Real)) where
  constraintCount : Nat
  normal : Fin constraintCount -> Fin d -> Real
  bound : Fin constraintCount -> Real
  mem_iff : forall x, x ∈ region <->
    forall j, typeIIAffineValue (normal j) x <= bound j

/-- The normal obtained by restricting a full inequality to canonical
sum-one completions. -/
def typeIIProjectedAffineNormal {k : Nat}
    (normal : Fin (k + 1) -> Real) : Fin k -> Real :=
  fun i => normal i.castSucc - normal (Fin.last k)

/-- The bound obtained by restricting a full inequality to canonical
sum-one completions. -/
def typeIIProjectedAffineBound {k : Nat}
    (normal : Fin (k + 1) -> Real) (bound : Real) : Real :=
  bound - normal (Fin.last k)

/-- Canonical completion turns a full affine value into its last coefficient
plus the projected affine value. -/
theorem typeIIAffineValue_completeProjectedLogTuple
    {k : Nat} (normal : Fin (k + 1) -> Real) (x : Fin k -> Real) :
    typeIIAffineValue normal (completeProjectedLogTuple x) =
      normal (Fin.last k) +
        typeIIAffineValue (typeIIProjectedAffineNormal normal) x := by
  rw [typeIIAffineValue, Fin.sum_univ_castSucc]
  simp only [completeProjectedLogTuple, Fin.snoc_castSucc, Fin.snoc_last,
    typeIIProjectedAffineNormal, typeIIAffineValue]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

namespace TypeIIAffineHalfspacePresentation

/-- Pull a full finite halfspace presentation back to the canonical
first-coordinate projection. -/
def projected {k : Nat} {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region) :
    TypeIIAffineHalfspacePresentation (typeIIProjectedRegion region) where
  constraintCount := presentation.constraintCount
  normal := fun j => typeIIProjectedAffineNormal (presentation.normal j)
  bound := fun j => typeIIProjectedAffineBound
    (presentation.normal j) (presentation.bound j)
  mem_iff := by
    intro x
    change completeProjectedLogTuple x ∈ region <-> _
    rw [presentation.mem_iff]
    constructor
    · intro hx j
      have hj := hx j
      rw [typeIIAffineValue_completeProjectedLogTuple] at hj
      dsimp only [typeIIProjectedAffineBound]
      linarith
    · intro hx j
      have hj := hx j
      dsimp only [typeIIProjectedAffineBound] at hj
      rw [typeIIAffineValue_completeProjectedLogTuple]
      linarith

end TypeIIAffineHalfspacePresentation

end

end PrimesRestrictedDigits
