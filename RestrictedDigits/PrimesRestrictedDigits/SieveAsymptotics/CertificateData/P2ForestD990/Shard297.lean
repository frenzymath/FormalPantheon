import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 297
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard297

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'left')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![819983 / 8000000, 105003 / 6400000, 105003 / 6400000],
    ![399991 / 4000000, 395013 / 16000000, 245007 / 16000000],
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![23333 / 200000, 11667 / 1000000, 0]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 44232077 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 65795282 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 67311584 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 78306974 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 70643613 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 88617954 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 90227717 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 103137976 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 118424196 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 101135298 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 123829389 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 114341254 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 138382779 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 129560677 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 152741368 / 1000000 }
            )
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 132270308 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 153233387 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 132144587 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 155702415 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 120520487 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 143826075 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 148389517 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 158662567 / 1000000 }
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
      (22201750506364703408151 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard297
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
