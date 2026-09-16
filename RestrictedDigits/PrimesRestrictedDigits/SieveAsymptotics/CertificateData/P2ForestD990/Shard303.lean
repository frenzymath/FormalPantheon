import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 303
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard303

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'right'), (4, 'left')), 26 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 105003 / 8000000, 105003 / 8000000],
    ![100831 / 1000000, 9267 / 320000, 35001 / 8000000],
    ![37999 / 400000, 255009 / 8000000, 105003 / 8000000],
    ![23333 / 200000, 11667 / 1000000, 0]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.split (2 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 1
                    middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 17823536 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 1
                    middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 25025991 / 1000000 }
                )
              )
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 9
                    middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 26065440 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 9
                    middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 26796469 / 1000000 }
                )
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 39522053 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 49520300 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 57635464 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 56817696 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 55934151 / 1000000 }
              )
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 49411817 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 55928713 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 57937232 / 1000000 }
              )
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 75097364 / 1000000 }
              )
              (.split (3 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 9
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 77792619 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 8
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 72034311 / 1000000 }
                )
              )
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 87090932 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 82029982 / 1000000 }
              )
            )
          )
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 101661448 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 112144963 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 93648540 / 1000000 }
            )
          )
        )
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 85758661 / 1000000 }
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 88101394 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 109756253 / 1000000 }
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 116799129 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 142031150 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 148030150 / 1000000 }
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
      (66119025354748149881763 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard303
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
