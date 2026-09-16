import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 317
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard317

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'right'), (2, 'left'), (5, 'left'), (4, 'left')), 29 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![181661 / 2000000, 11667 / 2000000, 0],
    ![181661 / 2000000, 8667 / 200000, 0],
    ![100831 / 1000000, 81669 / 8000000, 35001 / 8000000],
    ![23333 / 200000, 11667 / 1000000, 0]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 0
                    middle := ![2, 2, 2, 2, 2, 2, 12, 0]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 4033965 / 1000000 }
                )
                (.split (2 : Fin 6)
                  (.retain
                    { baseline := 1
                      legacy := 1
                      middle := ![2, 2, 2, 2, 2, 2, 2, 8]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 8604068 / 1000000 }
                  )
                  (.retain
                    { baseline := 1
                      legacy := 0
                      middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 6957101 / 1000000 }
                  )
                )
              )
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 10587753 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 10338428 / 1000000 }
                )
              )
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 9086513 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 4977872 / 1000000 }
              )
            )
          )
          (.split (1 : Fin 6)
            (.split (1 : Fin 6)
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 14029569 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 9885169 / 1000000 }
                )
              )
              (.split (2 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 8339321 / 1000000 }
                )
                (.split (2 : Fin 6)
                  (.retain
                    { baseline := 1
                      legacy := 8
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 11813396 / 1000000 }
                  )
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 14853568 / 1000000 }
                  )
                )
              )
            )
            (.split (2 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 0
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 3227987 / 1000000 }
                )
                (.split (5 : Fin 6)
                  (.retain
                    { baseline := 0
                      legacy := 12
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 8232628 / 1000000 }
                  )
                  (.retain
                    { baseline := 8
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 7447565 / 1000000 }
                  )
                )
              )
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 3449147 / 1000000 }
              )
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (5 : Fin 6)
              (.split (2 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 21762966 / 1000000 }
                )
                (.split (4 : Fin 6)
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 20910921 / 1000000 }
                  )
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 17068233 / 1000000 }
                  )
                )
              )
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 27834937 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 19648933 / 1000000 }
                )
              )
            )
            (.split (5 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 8
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 26803298 / 1000000 }
                )
                (.retain
                  { baseline := 8
                    legacy := 2
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 26803623 / 1000000 }
                )
              )
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 30207200 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 18028361 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 18356594 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 27057047 / 1000000 }
          )
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 7967069 / 1000000 }
        )
      )
    )
    (.retain
      { baseline := 8
        legacy := 2
        middle := ![2, 2, 2, 2, 2, 2, 2, 2]
        inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
        upper := 17905262 / 1000000 }
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (95293142931544242321429 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard317
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
