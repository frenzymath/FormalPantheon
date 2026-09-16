import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 4
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard004

/- Root 0, exact path ((0, 'left'), (2, 'left'), (0, 'left'), (2, 'right'), (0, 'left'), (3, 'left')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![1154999 / 8000000, 455013 / 16000000, 455013 / 16000000],
    ![156667 / 1000000, 11667 / 400000, 35001 / 2000000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![1295003 / 8000000, 35001 / 3200000, 35001 / 3200000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
                  upper := 37323938 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
                  upper := 44166215 / 1000000 }
              )
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 25, 17, 1, 1, 1, 1]
                  upper := 32652716 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 25, 17, 1, 1, 1, 1]
                  upper := 41468920 / 1000000 }
              )
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 17, 1, 1, 1, 1]
                upper := 30136406 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 17, 1, 1, 1, 1]
                upper := 38948913 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
                upper := 14994880 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 22979142 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 29010974 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 37820956 / 1000000 }
            )
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
                upper := 41081038 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
                upper := 42922835 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 47192143 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 17, 1, 1, 1, 1]
              upper := 38812682 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 44195001 / 1000000 }
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 49970316 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 51822381 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
            upper := 56092228 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
            upper := 63806846 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 17, 1, 1, 1]
              upper := 67373703 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 1, 1, 1]
                upper := 78968186 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 1, 1, 1]
                upper := 82762119 / 1000000 }
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
      (9867001778759814837687 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard004
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
