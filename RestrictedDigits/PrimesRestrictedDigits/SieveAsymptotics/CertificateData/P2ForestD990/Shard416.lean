import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 416
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard416

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'right'), (1, 'right'), (2, 'right'), (1, 'right'), (2, 'right')), 27 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000],
    ![399991 / 4000000, 459 / 15625, 459 / 15625],
    ![52499 / 500000, 355011 / 16000000, 355011 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 14, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 197175280 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 187281537 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 201525419 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 196681038 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 176329583 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 177587436 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 173937117 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 163074754 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 173868861 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 163612507 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 161827984 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 153266610 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 151938879 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 140732946 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 153724935 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 145257115 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 14, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 207523907 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 197069865 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 182275117 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 177532507 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 169130174 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 174775715 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 169616062 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 156537590 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 177714011 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 175681537 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 169135946 / 1000000 }
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
      (210662815623214144124547 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard416
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
