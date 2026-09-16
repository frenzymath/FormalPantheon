import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronClosedClipD1002

/-!
# Composition of exact closed I6 certificate subtrees

The replay is exactly volume-weighted retained list. Structural equations reuse checked
subtrees without reevaluating their leaf payloads. Source: `MAYNARD-PRD-PUBLISHED`, Section 6,
p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

def RationalTetraClipD1002.replayWeightRatD1010 {n : Nat}
    (tree : RationalTetraClipD1002 n Rat) (walls : Fin n -> RationalAffine 3)
    (T : RationalTetrahedron) : Rat :=
  ((tree.retainedLeaves walls T).map (fun leaf => leaf.1.volumeRat * leaf.2)).sum

namespace SectionSixI6CertificateD1010

variable {n : Nat} {walls : Fin n -> RationalAffine 3}
  {payloadValid : RationalTetrahedron -> Rat -> Bool} {T : RationalTetrahedron}

theorem valid_split {e : Fin 6} {r : Rat} {left right : RationalTetraClipD1002 n Rat}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hl : left.coverValid walls payloadValid
      (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).1 (T.edgePointD1000 e r)) = true)
    (hh : right.coverValid walls payloadValid
      (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).2 (T.edgePointD1000 e r)) = true) :
    (RationalTetraClipD1002.split e r left right).coverValid walls payloadValid T = true := by
  simp only [RationalTetraClipD1002.coverValid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hr0, hr1⟩, hl⟩, hh⟩

theorem valid_zeroFace {w : Fin n} {pivot : Fin 4} {child : RationalTetraClipD1002 n Rat}
    (hnonpos : ∀ i, rationalAffineEval_D969 (walls w) (T.vertex i) <= 0)
    (hpivot : rationalAffineEval_D969 (walls w) (T.vertex pivot) = 0)
    (hchild : child.coverValid walls payloadValid
      (T.zeroVertexFaceD1001 (walls w) pivot) = true) :
    (RationalTetraClipD1002.zeroFace w pivot child).coverValid walls payloadValid T = true := by
  simp only [RationalTetraClipD1002.coverValid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hnonpos, hpivot⟩, hchild⟩

theorem replay_split {e : Fin 6} {r a b : Rat} {left right : RationalTetraClipD1002 n Rat}
    (hl : left.replayWeightRatD1010 walls
      (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).1 (T.edgePointD1000 e r)) = a)
    (hr : right.replayWeightRatD1010 walls
      (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).2 (T.edgePointD1000 e r)) = b) :
    (RationalTetraClipD1002.split e r left right).replayWeightRatD1010 walls T = a + b := by
  rw [RationalTetraClipD1002.replayWeightRatD1010, RationalTetraClipD1002.retainedLeaves,
    List.map_append, List.sum_append]
  change left.replayWeightRatD1010 walls
    (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).1 (T.edgePointD1000 e r)) +
    right.replayWeightRatD1010 walls
      (T.replaceVertex (RationalTetrahedron.edgeEndpoints e).2 (T.edgePointD1000 e r)) = a + b
  rw [hl, hr]

theorem replay_zeroFace {w : Fin n} {pivot : Fin 4} {a : Rat}
    {child : RationalTetraClipD1002 n Rat}
    (hchild : child.replayWeightRatD1010 walls (T.zeroVertexFaceD1001 (walls w) pivot) = a) :
    (RationalTetraClipD1002.zeroFace w pivot child).replayWeightRatD1010 walls T = a :=
  hchild

end SectionSixI6CertificateD1010
end PrimesRestrictedDigits
