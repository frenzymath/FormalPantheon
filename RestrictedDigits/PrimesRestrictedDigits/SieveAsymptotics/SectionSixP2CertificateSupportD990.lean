import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988

/-!
# Composition of exact P2 certificate shards

The defining split equations specialize to payloads. Assembly can reuse checked subtrees
without evaluating their leaf weights again. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs.
(6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits.SectionSixP2CertificateD990

theorem valid_split {T : RationalTetrahedron} {e : Fin 6}
    {left right : RationalTetraSubdivision SectionSixP2LeafPayloadD988}
    (hl : left.coverValid sectionSixP2LeafValidD988 (T.leftChild e) = true)
    (hr : right.coverValid sectionSixP2LeafValidD988 (T.rightChild e) = true) :
    (RationalTetraSubdivision.split e left right).coverValid
      sectionSixP2LeafValidD988 T = true := by
  change (left.coverValid sectionSixP2LeafValidD988 (T.leftChild e) &&
    right.coverValid sectionSixP2LeafValidD988 (T.rightChild e)) = true
  rw [hl, hr]
  rfl

theorem replay_split {T : RationalTetrahedron} {e : Fin 6}
    {left right : RationalTetraSubdivision SectionSixP2LeafPayloadD988} {a b : Rat}
    (hl : left.replayWeightRat (T.leftChild e) (fun _ p => p.upper) = a)
    (hr : right.replayWeightRat (T.rightChild e) (fun _ p => p.upper) = b) :
    (RationalTetraSubdivision.split e left right).replayWeightRat T
      (fun _ p => p.upper) = a + b := by
  change left.replayWeightRat (T.leftChild e) (fun _ p => p.upper) +
    right.replayWeightRat (T.rightChild e) (fun _ p => p.upper) = a + b
  rw [hl, hr]

end PrimesRestrictedDigits.SectionSixP2CertificateD990
