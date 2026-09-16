import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 408
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard408

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'right'), (3, 'right'), (0, 'right')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000],
    ![399991 / 4000000, 192507 / 4000000, 459 / 15625],
    ![399991 / 4000000, 460017 / 8000000, 459 / 15625],
    ![52499 / 500000, 29001 / 800000, 29001 / 800000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 213044614 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 213010621 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 202203924 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 213294374 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 227161033 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 220355021 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 213518177 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 207251370 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 208272406 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 15, 15, 15, 15, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
            upper := 217738928 / 1000000 }
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 226478199 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 225081658 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 212076959 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 213175898 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 226496201 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 243098654 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 238725647 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 234307127 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 222167784 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 232797373 / 1000000 }
              )
            )
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 257171279 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 252837276 / 1000000 }
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
      (107244231325800581833263 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard408
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
