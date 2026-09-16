import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 419
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard419

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'left'), (3, 'left'), (2, 'left'), (4, 'right')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![359989 / 4000000, 53127 / 1000000, 53127 / 1000000],
    ![84997 / 1000000, 26001 / 400000, 185007 / 4000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![84997 / 1000000, 26001 / 400000, 445017 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 457763746 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                  upper := 486183884 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 463961124 / 1000000 }
              )
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 550974089 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 520015835 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 540415760 / 1000000 }
              )
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 449474387 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 501456768 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 455342220 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 453212016 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 423952456 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 424250558 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 411028999 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 441345015 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 408253176 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 376068597 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 377064781 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 362900811 / 1000000 }
              )
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 398317109 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 364664885 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 420410734 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 384193878 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 384853535 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 361168803 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 410991177 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 375333540 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 360145886 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 409840229 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 374417678 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 360930177 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 361885082 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 348107804 / 1000000 }
              )
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
      (988546356219046194058509 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard419
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
