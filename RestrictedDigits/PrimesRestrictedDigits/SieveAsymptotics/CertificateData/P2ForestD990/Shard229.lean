import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 229
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard229

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'left'), (5, 'left'), (4, 'right'), (0, 'left'), (3, 'right')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![391657 / 4000000, 63669 / 1600000, 35001 / 4000000],
    ![181661 / 2000000, 248343 / 4000000, 0],
    ![383323 / 4000000, 95337 / 1600000, 35001 / 16000000],
    ![414991 / 4000000, 445017 / 8000000, 0]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 8
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 12563532 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 8
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 20356083 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 18436429 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 26319022 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 22053688 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 34390541 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 48035176 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 58095443 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 47556706 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 41633461 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 26725342 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 47878540 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 20901645 / 1000000 }
      )
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 38260665 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 35782707 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 53169006 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33383764 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 49065586 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 64216606 / 1000000 }
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
      (4836587216785489376919 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard229
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
