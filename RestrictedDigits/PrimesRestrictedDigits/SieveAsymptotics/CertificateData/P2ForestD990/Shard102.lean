import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 102
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard102

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right'), (0, 'left'), (0, 'right'), (2, 'left'), (4, 'left'), (2, 'left')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![180997 / 1600000, 35001 / 16000000, 35001 / 16000000],
    ![27187 / 250000, 105003 / 16000000, 105003 / 16000000],
    ![23333 / 200000, 11667 / 1000000, 0],
    ![244997 / 2000000, 0, 0]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 8767267 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 7384648 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 9959897 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 20538883 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 17575401 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22001145 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 16064517 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 18513690 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 16552012 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 2, 8]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 22347146 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (2 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22323190 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 26892147 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 8]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 20494620 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 2, 8]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 26411169 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 38705498 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 35616614 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![2, 2, 2, 2, 2, 2, 14, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 44637566 / 1000000 }
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (2396269981094354328843 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard102
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
