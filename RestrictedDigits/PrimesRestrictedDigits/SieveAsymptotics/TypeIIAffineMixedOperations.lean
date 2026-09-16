import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddedAffineNormal

/-!
# Operations on mixed affine presentations

This module exposes the small closure API needed by the terminal-`V` target. Constraint
families are concatenated with `Fin.append`; no constraints are deduplicated, so occurrence
multiplicity and strictness tags are preserved.
-/

namespace PrimesRestrictedDigits

/-- View a weak affine presentation as a mixed presentation with no strict
walls. -/
def TypeIIAffineHalfspacePresentation.toMixed
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region) :
    TypeIIAffineMixedPresentation region where
  constraintCount := presentation.constraintCount
  normal := presentation.normal
  bound := presentation.bound
  isStrict := fun _ => false
  mem_iff := by
    intro x
    simpa using presentation.mem_iff x

/-- Intersect two mixed presentations by appending their constraint families.
Every original wall, including duplicate walls, remains an occurrence. -/
def TypeIIAffineMixedPresentation.inter
    {d : Nat} {leftRegion rightRegion : Set (Fin d -> Real)}
    (left : TypeIIAffineMixedPresentation leftRegion)
    (right : TypeIIAffineMixedPresentation rightRegion) :
    TypeIIAffineMixedPresentation (leftRegion ∩ rightRegion) where
  constraintCount := left.constraintCount + right.constraintCount
  normal := Fin.append left.normal right.normal
  bound := Fin.append left.bound right.bound
  isStrict := Fin.append left.isStrict right.isStrict
  mem_iff := by
    intro x
    rw [Set.mem_inter_iff, left.mem_iff, right.mem_iff,
      Fin.forall_fin_add]
    constructor
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩

/-- Pull a mixed presentation back along an injective coordinate embedding.
Normals are extended by zero away from the embedding image, while bounds and
strictness tags are unchanged. -/
noncomputable def TypeIIAffineMixedPresentation.liftAlongEmbedding
    {s r : Nat} {region : Set (Fin s -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (embedding : Fin s ↪ Fin r) :
    TypeIIAffineMixedPresentation
      (typeIIAffineEmbeddingPreimageRegion embedding region) where
  constraintCount := presentation.constraintCount
  normal := fun j => typeIIAffineLiftNormal embedding (presentation.normal j)
  bound := presentation.bound
  isStrict := presentation.isStrict
  mem_iff := by
    intro x
    change (fun i => x (embedding i)) ∈ region ↔ _
    rw [presentation.mem_iff]
    constructor
    · intro hx j
      have hj := hx j
      simpa only [typeIIAffineValue_liftNormal] using hj
    · intro hx j
      have hj := hx j
      simpa only [typeIIAffineValue_liftNormal] using hj

end PrimesRestrictedDigits
