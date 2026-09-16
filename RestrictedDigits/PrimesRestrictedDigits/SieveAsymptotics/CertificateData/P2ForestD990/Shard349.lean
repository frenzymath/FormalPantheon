import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 349
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard349

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'left'), (5, 'right')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![229997 / 2000000, 200007 / 4000000, 35001 / 1600000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![229997 / 2000000, 200007 / 4000000, 31251 / 1000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 139715760 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                  upper := 141022602 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 136276802 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 148681680 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 139607071 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 136596703 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 143869492 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 126204340 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 122018215 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 132450400 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 161246420 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 168000405 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 153007002 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 140721655 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 128524726 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 143439413 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 135017130 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 129186870 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 123729910 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 124439907 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 118231862 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 115018412 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 136111897 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 130364204 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 124814227 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                  upper := 130584187 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                  upper := 127023108 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 121502133 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                  upper := 119683404 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 120629400 / 1000000 }
              )
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 115727729 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 116522429 / 1000000 }
              )
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
      (160889702605917211573101 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard349
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
