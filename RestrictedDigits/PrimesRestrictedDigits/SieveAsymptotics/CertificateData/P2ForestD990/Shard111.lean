import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 111
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard111

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right'), (0, 'right'), (2, 'right'), (1, 'left')), 16 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![181661 / 2000000, 11667 / 2000000, 0],
    ![84997 / 1000000, 35001 / 4000000, 35001 / 4000000],
    ![23333 / 200000, 11667 / 1000000, 0],
    ![374989 / 4000000, 0, 0]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 16945404 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 0
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 6605714 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 12031139 / 1000000 }
                )
              )
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 0
                    middle := ![2, 2, 2, 2, 2, 2, 12, 12]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 8313789 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 12358808 / 1000000 }
                )
              )
            )
            (.split (1 : Fin 6)
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 0
                    legacy := 12
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 6738108 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 15063414 / 1000000 }
                )
              )
              (.split (0 : Fin 6)
                (.retain
                  { baseline := 0
                    legacy := 12
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 20078527 / 1000000 }
                )
                (.retain
                  { baseline := 8
                    legacy := 2
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 3539681 / 1000000 }
                )
              )
            )
          )
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 22121002 / 1000000 }
              )
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 30672689 / 1000000 }
                )
                (.retain
                  { baseline := 8
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 34354111 / 1000000 }
                )
              )
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 18481033 / 1000000 }
            )
          )
        )
      )
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 19051111 / 1000000 }
      )
    )
    (.split (3 : Fin 6)
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 51150903 / 1000000 }
      )
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 82654844 / 1000000 }
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (4250523133228361606001 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard111
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
