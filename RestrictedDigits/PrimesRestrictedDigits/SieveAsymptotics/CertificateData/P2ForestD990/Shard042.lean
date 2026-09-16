import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 42
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard042

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'right'), (1, 'right'), (2, 'left'), (2, 'right'), (0, 'left')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![994991 / 8000000, 315009 / 16000000, 315009 / 16000000],
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![1064993 / 8000000, 35001 / 3200000, 35001 / 3200000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 58047746 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 53882083 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 50676378 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 60484204 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 56961179 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 65486058 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 70498660 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 70254408 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 89315579 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 88146071 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 77588441 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 79300963 / 1000000 }
            )
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 61976273 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 63682106 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 69947369 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 72926561 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 79222660 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 13, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 85453994 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 84324750 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 95820163 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 83161878 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 82323750 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 92989036 / 1000000 }
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
      (146040011709982567353 / 16384000000000000000000000 : Rat) := by
  decide +kernel

end Shard042
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
