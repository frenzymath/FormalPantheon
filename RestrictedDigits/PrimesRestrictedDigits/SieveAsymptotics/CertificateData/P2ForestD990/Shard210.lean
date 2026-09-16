import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 210
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard210

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (3, 'left'), (3, 'left'), (2, 'right'), (1, 'left')), 24 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 29001 / 800000, 35001 / 2000000],
    ![399991 / 4000000, 460017 / 8000000, 245007 / 16000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000],
    ![221663 / 2000000, 66669 / 2000000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 89619920 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 96883644 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 103030801 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 112277981 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 108304896 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 116820372 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 122117849 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 14, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 116173190 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 14, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 123888280 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 115908135 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 123551478 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 127825951 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 130640000 / 1000000 }
            )
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 87049620 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 93754530 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 99489741 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 104435099 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 110883843 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 120658927 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 113555182 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 119161838 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 126208165 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 119351206 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 127589824 / 1000000 }
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
      (83814092111860540955001 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard210
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
