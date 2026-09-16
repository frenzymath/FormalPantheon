import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 338
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard338

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'left'), (2, 'right'), (3, 'right'), (2, 'left')), 30 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![519997 / 4000000, 455013 / 16000000, 455013 / 16000000],
    ![124999 / 1000000, 90003 / 2000000, 105003 / 4000000],
    ![229997 / 2000000, 200007 / 4000000, 325011 / 8000000],
    ![269999 / 2000000, 245007 / 8000000, 245007 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 25, 17]
                upper := 116235781 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 25]
                upper := 114961052 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 25]
              upper := 120661056 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 25]
                upper := 123792879 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
                upper := 117349370 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
              upper := 113281919 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 25]
                upper := 125572370 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
                upper := 120287158 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 25]
              upper := 115365107 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 25]
              upper := 110951022 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 25]
                upper := 110064062 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 109964057 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 139942884 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 141215480 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 140288754 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 153595599 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 150986663 / 1000000 }
              )
            )
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 144462598 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 144160969 / 1000000 }
              )
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 136915819 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 129835925 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 130999621 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 123331545 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 132434193 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 131817318 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 127362815 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 125785401 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 119806000 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 116480877 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 118493371 / 1000000 }
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
      (73552364188763206414257 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard338
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
