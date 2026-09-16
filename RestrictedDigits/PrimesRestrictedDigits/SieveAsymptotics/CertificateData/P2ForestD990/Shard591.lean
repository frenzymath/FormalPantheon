import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 591
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard591

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (4, 'left'), (2, 'left'), (4, 'right'), (4, 'left'), (5, 'left')), 14 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![84997 / 1000000, 27501 / 1000000, 27501 / 1000000],
    ![779981 / 8000000, 905031 / 32000000, 455013 / 32000000],
    ![26399 / 320000, 1595061 / 32000000, 845031 / 32000000],
    ![399991 / 4000000, 395013 / 16000000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 222769038 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 266837110 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 295114845 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 287486278 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 320898121 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 202684037 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 227123773 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 280418248 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 203131873 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 254770833 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 214190654 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 194082114 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 228315643 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 281837532 / 1000000 }
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
      (60125598010871515652589 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard591
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
