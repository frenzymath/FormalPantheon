import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 383
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard383

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'right'), (2, 'right'), (1, 'right'), (2, 'right'), (0, 'left')), 14 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 29001 / 800000, 35001 / 2000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000],
    ![52499 / 500000, 215007 / 8000000, 215007 / 8000000],
    ![439993 / 4000000, 315009 / 16000000, 315009 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 154866019 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 158604575 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 167633827 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 14, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 141993379 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 144292442 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 155012900 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 162814262 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 170921521 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 171600257 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 14, 15, 15, 15, 15, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 147677858 / 1000000 }
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 14, 14, 15, 15, 15, 9, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 136007689 / 1000000 }
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 14, 15, 15, 15, 15, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 147425441 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 143997323 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 147793106 / 1000000 }
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
      (9094993333867444594887 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard383
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
