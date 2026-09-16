import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 430
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard430

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'right'), (3, 'left'), (1, 'left'), (1, 'left')), 30 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![149993 / 2000000, 485019 / 8000000, 485019 / 8000000],
    ![84997 / 1000000, 26001 / 400000, 185007 / 4000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 319836470 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 329884447 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 30]
                upper := 349505062 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 349365845 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 359991040 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 384777180 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 373822027 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 401257497 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 439095429 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 415563666 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 429122770 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 445328413 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 380430001 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 401937747 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 439791755 / 1000000 }
            )
          )
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
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 510899275 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 596637027 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 575470272 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 541412740 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 512552025 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 492883126 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 502006451 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 468446944 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 449334953 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 470820111 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 461369130 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 444081233 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 434793216 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 392589818 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 433983247 / 1000000 }
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
      (16426572506319037484979 / 128000000000000000000000000 : Rat) := by
  decide +kernel

end Shard430
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
