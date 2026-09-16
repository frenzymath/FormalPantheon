import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 238
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard238

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'right'), (0, 'right'), (0, 'right'), (2, 'right')), 28 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![37999 / 400000, 255009 / 8000000, 105003 / 8000000],
    ![84997 / 1000000, 26001 / 400000, 35001 / 4000000],
    ![391657 / 4000000, 63669 / 1600000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 123025127 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 133014721 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 135051712 / 1000000 }
              )
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 135883815 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 133326192 / 1000000 }
              )
            )
          )
        )
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 134873184 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 134870947 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 137076881 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 140869575 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 137590548 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 141098854 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 145131790 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 143853585 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 135375191 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 149744641 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 153717327 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 124443463 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 138709343 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 142383010 / 1000000 }
              )
            )
          )
          (.split (3 : Fin 6)
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 142903513 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 136528007 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 141735494 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 150720625 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 149575334 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 151061919 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 155417604 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 155196073 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 160087175 / 1000000 }
              )
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
      (12581735544969478331049 / 512000000000000000000000000 : Rat) := by
  decide +kernel

end Shard238
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
