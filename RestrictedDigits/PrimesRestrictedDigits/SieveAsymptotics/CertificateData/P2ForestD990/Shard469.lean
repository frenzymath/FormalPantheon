import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 469
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard469

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'right'), (4, 'left'), (5, 'left'), (4, 'right'), (1, 'left')), 28 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 82503 / 2000000, 87003 / 3200000],
    ![84997 / 1000000, 26001 / 400000, 27501 / 1000000],
    ![84997 / 1000000, 26001 / 400000, 295011 / 8000000],
    ![37999 / 400000, 240009 / 4000000, 90003 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 13
                  middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 214712576 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 223902559 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 233484496 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 253615105 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 260371931 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 244962098 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 285093075 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 307402439 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 298281925 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 288208749 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 277579095 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 261853160 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 211385123 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 218072580 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 226960153 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 258746942 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 239789339 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 260735446 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 252097380 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 238956498 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 258871049 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 273794312 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 283959514 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 275681967 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 263271603 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 278319378 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 264086071 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 256812724 / 1000000 }
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
      (620007095779380129550149 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard469
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
