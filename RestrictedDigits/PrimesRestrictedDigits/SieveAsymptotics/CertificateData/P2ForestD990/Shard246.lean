import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 246
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard246

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'right')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![284999 / 2000000, 35001 / 2000000, 0],
    ![23333 / 200000, 98337 / 2000000, 0],
    ![253331 / 2000000, 278343 / 8000000, 35001 / 8000000],
    ![518329 / 4000000, 341679 / 8000000, 0]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 8, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 7304625 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 8, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 7977974 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 15492416 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 11051469 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 8, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 14473066 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 8, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 9837645 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 8, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 2305108 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 8, 0, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 2979041 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 8, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 9314409 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 8, 0, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 6030523 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 8, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 4626737 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 12, 0, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 7247185 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 8, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 5332086 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 12, 0, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 3067757 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 8, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 7278538 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 9256888 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 11882677 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 8615919 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 3774269 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 0, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 2642865 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 2464514 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 5459372 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![0, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 8]
                upper := 2295672 / 1000000 }
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
      (19802091609165467502207 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard246
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
