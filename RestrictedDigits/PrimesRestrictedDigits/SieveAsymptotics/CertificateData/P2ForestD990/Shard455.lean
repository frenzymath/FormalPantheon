import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 455
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard455

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'right'), (4, 'left'), (5, 'left'), (4, 'left'), (1, 'right')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![37999 / 400000, 240009 / 4000000, 87003 / 3200000],
    ![399991 / 4000000, 545019 / 16000000, 395013 / 16000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 14, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 134918197 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 146762855 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 149931799 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 152873803 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 146831020 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 173868372 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 174482461 / 1000000 }
              )
            )
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 186545772 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 187390656 / 1000000 }
              )
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 161190897 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 165253595 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 183259626 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 193495808 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 196960085 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 179839671 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 167889550 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 163420927 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 155942347 / 1000000 }
              )
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 167609457 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 173196428 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 185374981 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 197053129 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 200538580 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 192376926 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 159719342 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 166249495 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 188103960 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 171947930 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 186868376 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 178987280 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 173709583 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 170504925 / 1000000 }
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
      (420975965381316760969461 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard455
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
