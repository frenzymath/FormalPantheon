import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 78
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard078

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'right'), (3, 'right')), 28 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![244997 / 2000000, 0, 0],
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![22583 / 200000, 11667 / 640000, 245007 / 16000000],
    ![914987 / 8000000, 245007 / 16000000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 113811539 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 111497617 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 116346669 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 13, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 123434676 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 109884737 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 13, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 116876364 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 114528512 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 102586926 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 123870315 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 124260806 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 121491130 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 110965640 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 143240813 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 146962625 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 127075859 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 119053651 / 1000000 }
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 107474735 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 102795387 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 93373605 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 95478361 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 89081187 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 84595895 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 88059704 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 14, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 78378786 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 64933701 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60136669 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 9, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 52490116 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 42403182 / 1000000 }
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (10145209309192017115407 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard078
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
