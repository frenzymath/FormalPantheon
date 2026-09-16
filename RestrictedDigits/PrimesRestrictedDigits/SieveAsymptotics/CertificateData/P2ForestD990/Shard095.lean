import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 95
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard095

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'left'), (3, 'right'), (3, 'right'), (3, 'right'), (4, 'right'), (1, 'right')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![23333 / 200000, 11667 / 1000000, 0],
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![11479 / 100000, 478347 / 32000000, 245007 / 32000000],
    ![454993 / 4000000, 35001 / 4000000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 13, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 77888003 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 85538359 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 87855227 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 80436195 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 100295004 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 95952745 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 128324167 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 113789748 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 109323039 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 68315994 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 60051751 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57860188 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45924286 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 32527203 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 14, 14, 15, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 67249837 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57912680 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 48641648 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 8, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33990481 / 1000000 }
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
      (7683332884043240255931 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard095
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
