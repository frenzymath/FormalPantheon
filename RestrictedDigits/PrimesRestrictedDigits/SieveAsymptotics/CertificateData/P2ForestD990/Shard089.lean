import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 89
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard089

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'left'), (3, 'right'), (3, 'left'), (1, 'right'), (0, 'left')), 31 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![237497 / 2000000, 245007 / 16000000, 105003 / 16000000],
    ![1888 / 15625, 151671 / 8000000, 105003 / 8000000],
    ![253331 / 2000000, 128337 / 8000000, 35001 / 8000000],
    ![244997 / 2000000, 0, 0]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 20474234 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 30161954 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 8, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 20697718 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 33089560 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 31130838 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 8, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 32484404 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 39967764 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 32741173 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 38659655 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 30778562 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33746090 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 30687332 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 34864710 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 42072272 / 1000000 }
              )
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 35915996 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 40131998 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 49415153 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45367120 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 14, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 56452635 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 15, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 68312622 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 49897194 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45331044 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 56946199 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 40264019 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 55612877 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 56388834 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 72785963 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 51083762 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 54540283 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 46341346 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 50777032 / 1000000 }
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
      (8601966976831140547899 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard089
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
