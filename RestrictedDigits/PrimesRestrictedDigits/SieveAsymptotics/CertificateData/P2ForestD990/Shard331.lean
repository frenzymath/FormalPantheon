import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 331
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard331

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'left'), (2, 'left'), (5, 'right'), (1, 'left'), (5, 'right')), 30 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![95999 / 800000, 685023 / 16000000, 685023 / 16000000],
    ![124999 / 1000000, 90003 / 2000000, 105003 / 4000000],
    ![52499 / 500000, 27501 / 500000, 27501 / 500000],
    ![229997 / 2000000, 200007 / 4000000, 200007 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                upper := 203751608 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                upper := 196016018 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                upper := 200132725 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 184395558 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                upper := 219542902 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 214459112 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                upper := 204959958 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 191917691 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                upper := 191353396 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                  upper := 190791258 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                  upper := 184402248 / 1000000 }
              )
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                upper := 188724892 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                upper := 183563503 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 178170790 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 180144915 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 31, 31, 31]
                upper := 183989344 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                  upper := 181450850 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 14, 31, 31, 31, 31, 31]
                  upper := 177859700 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 169172775 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 167645066 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 169500562 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 164494520 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 155778031 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 149379042 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 144620699 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 138458529 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 124562009 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 159979604 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 159013216 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 150841205 / 1000000 }
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
      (16907845566378854781819 / 655360000000000000000000000 : Rat) := by
  decide +kernel

end Shard331
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
