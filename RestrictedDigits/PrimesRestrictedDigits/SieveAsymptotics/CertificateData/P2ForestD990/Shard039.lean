import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 39
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard039

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'right'), (1, 'left'), (3, 'right'), (3, 'right'), (3, 'right')), 20 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![1043327 / 8000000, 828357 / 32000000, 735021 / 32000000],
    ![284999 / 2000000, 35001 / 4000000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 53634581 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 29]
              upper := 64437953 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
              upper := 69794548 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 80791502 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 72961648 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 51955094 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 60930650 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 51599214 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
              upper := 44223183 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
              upper := 79798366 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 88243570 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 81450458 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
              upper := 82042581 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 100435511 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 85957436 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 73749937 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 86198645 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 64521275 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 59365399 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 54305781 / 1000000 }
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
      (6854362829083700741151 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard039
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
