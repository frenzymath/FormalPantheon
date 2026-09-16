import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 187
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard187

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'left'), (5, 'right'), (5, 'right'), (1, 'left'), (5, 'left')), 28 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![1888 / 15625, 301677 / 8000000, 105003 / 8000000],
    ![23333 / 200000, 98337 / 2000000, 0],
    ![22583 / 200000, 102087 / 2000000, 245007 / 16000000],
    ![1888 / 15625, 9417 / 200000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 67351859 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 63340913 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60105849 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 53035204 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 14, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 51612750 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 62438172 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 69782927 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 67896941 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 56281982 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 74856087 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 70725662 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 67758655 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 67925489 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 53131638 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 47801948 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 52936624 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 42324771 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 35521252 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 30915875 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 8, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 19607774 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33445243 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 55349078 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 70373333 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 49417159 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 54708118 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 67234274 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 69769462 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 13, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 66189094 / 1000000 }
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
      (171037101162597690309093 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard187
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
