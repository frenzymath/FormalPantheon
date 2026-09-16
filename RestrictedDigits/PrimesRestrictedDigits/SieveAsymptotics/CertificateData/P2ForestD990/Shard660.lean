import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 660
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard660

/- Root 2, exact path ((2, 'right'), (1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (2, 'left'), (4, 'left')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![149993 / 2000000, 27501 / 2000000, 27501 / 2000000],
    ![149993 / 2000000, 26001 / 800000, 27501 / 2000000],
    ![16249 / 250000, 225009 / 8000000, 225009 / 8000000],
    ![84997 / 1000000, 35001 / 4000000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 279181509 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 348487197 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 356113037 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 345129804 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 372922239 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 384140956 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 405822591 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 373513488 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 404166615 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 551018712 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 516176222 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 669912302 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 604686336 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 653253735 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 552083957 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 462457764 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 427491402 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 484532208 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 448144490 / 1000000 }
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
      (105170066132761850701617 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard660
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
