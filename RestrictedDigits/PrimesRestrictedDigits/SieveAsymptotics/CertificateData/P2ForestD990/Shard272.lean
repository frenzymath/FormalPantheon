import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 272
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard272

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (5, 'right'), (3, 'right'), (2, 'right'), (0, 'right')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![23333 / 200000, 11667 / 1000000, 0],
    ![23333 / 200000, 121671 / 4000000, 0],
    ![221663 / 2000000, 66669 / 2000000, 35001 / 4000000],
    ![11479 / 100000, 478347 / 32000000, 245007 / 32000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 14, 15, 9, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 54897057 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 52632430 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45010290 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45495853 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 45840444 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 41610433 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 8, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22815218 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 8, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33533316 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 31719381 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 46671076 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 38315565 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 26039228 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 23031466 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 8, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 12524462 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 44703766 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 25472083 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22463454 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 16747524 / 1000000 }
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
      (2040203314505606513841 / 655360000000000000000000000 : Rat) := by
  decide +kernel

end Shard272
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
