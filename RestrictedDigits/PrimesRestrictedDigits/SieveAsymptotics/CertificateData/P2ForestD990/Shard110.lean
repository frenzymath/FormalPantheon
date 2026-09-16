import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 110
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard110

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right'), (0, 'right'), (2, 'left'), (4, 'right')), 24 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![374989 / 4000000, 0, 0],
    ![84997 / 1000000, 35001 / 4000000, 35001 / 4000000],
    ![23333 / 200000, 11667 / 1000000, 0],
    ![414991 / 4000000, 35001 / 8000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 45323260 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 33068726 / 1000000 }
                )
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 20394625 / 1000000 }
              )
            )
            (.split (3 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 19704264 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 0
                    middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 14308619 / 1000000 }
                )
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 18215384 / 1000000 }
              )
            )
          )
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 33197397 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 10
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 29382014 / 1000000 }
                )
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 14827877 / 1000000 }
              )
            )
            (.split (0 : Fin 6)
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 29910203 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 10
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 26194831 / 1000000 }
                )
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 18198527 / 1000000 }
              )
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 40061419 / 1000000 }
              )
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 33899219 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 31605385 / 1000000 }
                )
              )
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 43133517 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 45820654 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 33400399 / 1000000 }
          )
        )
      )
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 33492578 / 1000000 }
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 67666908 / 1000000 }
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 56888020 / 1000000 }
        )
      )
      (.split (3 : Fin 6)
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 77224598 / 1000000 }
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 100160180 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 120231913 / 1000000 }
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
      (5501309631251767118577 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard110
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
