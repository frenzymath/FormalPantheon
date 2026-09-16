import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 454
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard454

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'right'), (4, 'left'), (5, 'left'), (4, 'left'), (1, 'left')), 24 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![399991 / 4000000, 545019 / 16000000, 395013 / 16000000],
    ![37999 / 400000, 240009 / 4000000, 87003 / 3200000],
    ![37999 / 400000, 81003 / 1600000, 255009 / 8000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 140139254 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 150921679 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 159717646 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 164768169 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 160590119 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 186443296 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 189221540 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 177947318 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 169704560 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 14, 14, 15, 15, 15, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 176583064 / 1000000 }
              )
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 181037385 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 185963136 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 192050170 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 194571087 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 187550482 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 201222018 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 197819736 / 1000000 }
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 198209872 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 212759463 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![2, 14, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 208935520 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![2, 14, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 219006341 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 210379848 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 14, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 209997142 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 14, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 208935363 / 1000000 }
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
      (93868412220452661666831 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard454
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
