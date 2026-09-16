import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 180
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard180

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'left'), (5, 'left'), (4, 'right'), (3, 'left')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![253331 / 2000000, 176673 / 4000000, 35001 / 8000000],
    ![68333 / 500000, 612 / 15625, 35001 / 4000000],
    ![284999 / 2000000, 29001 / 800000, 0]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 25, 1]
                upper := 22304697 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 8, 17]
                upper := 17485767 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 8, 17]
                upper := 12209548 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 8, 17]
                upper := 16051672 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
                  upper := 26028190 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
                  upper := 30596673 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
                upper := 22209237 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
              upper := 24919626 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
                upper := 25484023 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
                  upper := 32032819 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
                  upper := 31280084 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
              upper := 28217641 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
            upper := 26265819 / 1000000 }
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 8, 17]
                upper := 9612608 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                upper := 17745962 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
              upper := 20127820 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
              upper := 18629810 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 24]
                upper := 17619603 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                upper := 22698942 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                  upper := 17993340 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 18429537 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 22608701 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 24046817 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 1
                    middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                    upper := 21332515 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 1
                    middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                    upper := 23827488 / 1000000 }
                )
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 22706250 / 1000000 }
              )
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                  upper := 19928523 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 25494609 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 27249671 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                  upper := 21011125 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                  upper := 26718721 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 29608562 / 1000000 }
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
      (26158303681929476777457 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard180
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
