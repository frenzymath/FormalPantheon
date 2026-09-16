import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 417
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard417

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'left'), (3, 'left'), (2, 'left'), (4, 'left'), (2, 'left')), 20 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![699977 / 8000000, 236259 / 4000000, 236259 / 4000000],
    ![84997 / 1000000, 26001 / 400000, 445017 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![84997 / 1000000, 26001 / 400000, 26001 / 400000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 415799409 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 413533446 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 389667326 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 391567927 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 378572884 / 1000000 }
            )
            (.split (2 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                  upper := 378468747 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                  upper := 374465378 / 1000000 }
              )
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 508106550 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 545003632 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 457734837 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 440347256 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 420023702 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 391353094 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 454987865 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 525089752 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 437794416 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 406843054 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
            upper := 405347810 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 376272361 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 376359883 / 1000000 }
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
      (1022508762748147664777853 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard417
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
