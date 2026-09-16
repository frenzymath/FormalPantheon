import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 293
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard293

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'right'), (3, 'right'), (5, 'right'), (0, 'left')), 27 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![181661 / 2000000, 8667 / 200000, 0],
    ![16249 / 250000, 75003 / 1000000, 0],
    ![84997 / 1000000, 185007 / 4000000, 35001 / 4000000],
    ![100831 / 1000000, 381681 / 8000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.split (5 : Fin 6)
                (.split (4 : Fin 6)
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 52979069 / 1000000 }
                  )
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 48630556 / 1000000 }
                  )
                )
                (.split (5 : Fin 6)
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 55622371 / 1000000 }
                  )
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 64984249 / 1000000 }
                  )
                )
              )
              (.split (5 : Fin 6)
                (.split (2 : Fin 6)
                  (.retain
                    { baseline := 9
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 48500906 / 1000000 }
                  )
                  (.retain
                    { baseline := 8
                      legacy := 14
                      middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                      inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                      upper := 44068302 / 1000000 }
                  )
                )
                (.retain
                  { baseline := 8
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 56939587 / 1000000 }
                )
              )
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 53108717 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 51621191 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 42228678 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 63549751 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 76662005 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 46339410 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 71016692 / 1000000 }
          )
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 58610881 / 1000000 }
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 82578785 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 93898912 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 59812754 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 72376493 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 89681290 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 69466261 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 35787891 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 45800386 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 39141023 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 40763609 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 56572364 / 1000000 }
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22000491 / 1000000 }
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
      (664596695952860867172351 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard293
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
