import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 577
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard577

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (1, 'right'), (2, 'left'), (4, 'right'), (4, 'left'), (1, 'left')), 20 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![149993 / 2000000, 595023 / 16000000, 595023 / 16000000],
    ![149993 / 2000000, 485019 / 8000000, 26001 / 800000],
    ![16249 / 250000, 75003 / 1600000, 75003 / 1600000],
    ![84997 / 1000000, 185007 / 4000000, 27501 / 1000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 385427359 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 434883484 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 451788820 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 434197298 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 591724068 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 661305327 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 535398495 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 507595198 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 509209986 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 466780848 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 540798971 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 604423850 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 692523749 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 643414059 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 533485901 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 596091236 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 470950731 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 513638847 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 500406343 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 544202531 / 1000000 }
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
      (4842322809750995165469 / 64000000000000000000000000 : Rat) := by
  decide +kernel

end Shard577
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
