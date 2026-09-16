import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0LeafValidatorD970

/-!
# Composition of exact P0 certificate shards

These are the defining split equations, specialized to the leaf validator. They let assembly
reuse checked shards without reducing them again. Source: `MAYNARD-PRD-PUBLISHED`, Section 6,
Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits.SectionSixP0CertificateD972

theorem valid_split {T : RationalTetrahedron} {e : Fin 6}
    {left right : RationalTetraSubdivision Rat}
    (hl : left.coverValid sectionSixP0LeafValidD970 (T.leftChild e) = true)
    (hr : right.coverValid sectionSixP0LeafValidD970 (T.rightChild e) = true) :
    (RationalTetraSubdivision.split e left right).coverValid
      sectionSixP0LeafValidD970 T = true := by
  change (left.coverValid sectionSixP0LeafValidD970 (T.leftChild e) &&
    right.coverValid sectionSixP0LeafValidD970 (T.rightChild e)) = true
  rw [hl, hr]
  rfl

theorem replay_split {T : RationalTetrahedron} {e : Fin 6}
    {left right : RationalTetraSubdivision Rat} {a b : Rat}
    (hl : left.replayWeightRat (T.leftChild e) (fun _ q => q) = a)
    (hr : right.replayWeightRat (T.rightChild e) (fun _ q => q) = b) :
    (RationalTetraSubdivision.split e left right).replayWeightRat T
      (fun _ q => q) = a + b := by
  change left.replayWeightRat (T.leftChild e) (fun _ q => q) +
    right.replayWeightRat (T.rightChild e) (fun _ q => q) = a + b
  rw [hl, hr]

end PrimesRestrictedDigits.SectionSixP0CertificateD972
