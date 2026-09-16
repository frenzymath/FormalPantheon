import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 449
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard449

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'left'), (5, 'right'), (3, 'left'), (1, 'left')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![149993 / 2000000, 485019 / 8000000, 485019 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 525021 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![84997 / 1000000, 26001 / 400000, 185007 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 395959980 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 428618863 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 455434617 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 456921841 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 477163626 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 474320783 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 503475107 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 506171146 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 512521906 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 527649710 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 587974726 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 553487030 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 546642233 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 589647213 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 623827360 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 621734219 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 603639262 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 550833759 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 594194949 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 547396962 / 1000000 }
            )
            (.split (2 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 526967583 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 536388789 / 1000000 }
              )
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 567727059 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 612612673 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 530126253 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 572885842 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 560594263 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 537152512 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 556368373 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 555217150 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 611651165 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 576333096 / 1000000 }
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
      (1276579060891120460259603 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard449
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
