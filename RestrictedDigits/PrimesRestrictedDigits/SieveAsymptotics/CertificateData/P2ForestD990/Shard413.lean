import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 413
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard413

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'right'), (1, 'right'), (2, 'right'), (1, 'left'), (3, 'left')), 21 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![399991 / 4000000, 459 / 15625, 459 / 15625],
    ![399991 / 4000000, 192507 / 4000000, 459 / 15625],
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000],
    ![52499 / 500000, 215007 / 8000000, 215007 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 212104679 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 218233033 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 225292388 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 237970845 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 232775222 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 265376481 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 258280566 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 244512953 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 234909098 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (5 : Fin 6)
        (.split (0 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 14, 15, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 208445628 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 209339054 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 216095610 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 212645891 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 219579520 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 228206166 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 231839429 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 214585956 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 218180755 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 224820877 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 242627721 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 234287531 / 1000000 }
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
      (279115644592519382539017 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard413
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
