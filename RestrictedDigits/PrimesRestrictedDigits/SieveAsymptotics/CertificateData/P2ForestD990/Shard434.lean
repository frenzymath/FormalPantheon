import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 434
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard434

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'right'), (3, 'left'), (1, 'right'), (0, 'right'), (2, 'left')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![399991 / 4000000, 459 / 15625, 459 / 15625],
    ![37999 / 400000, 82503 / 2000000, 255009 / 8000000],
    ![84997 / 1000000, 185007 / 4000000, 185007 / 4000000],
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (1 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 9
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 302195913 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 311753486 / 1000000 }
              )
            )
            (.split (2 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 303041946 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 304211569 / 1000000 }
              )
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 335949288 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 319560946 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 334525777 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 306269547 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 290574743 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 288056580 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 282499439 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 279910808 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 267346483 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 260721491 / 1000000 }
              )
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 294365906 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 287914406 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.split (0 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 285507474 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 285024380 / 1000000 }
              )
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 273834773 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 260486093 / 1000000 }
              )
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 298813779 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 326973608 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 325378529 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 292707872 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 284525048 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 283142008 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 278962495 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 271431141 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 9
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 271673522 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 260643828 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 264673861 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 258460143 / 1000000 }
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
      (88763150944172006459019 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard434
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
