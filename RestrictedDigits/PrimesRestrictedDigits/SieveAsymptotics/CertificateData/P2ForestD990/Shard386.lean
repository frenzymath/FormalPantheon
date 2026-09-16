import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 386
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard386

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 365013 / 8000000, 365013 / 8000000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![37999 / 400000, 240009 / 4000000, 240009 / 4000000],
    ![52499 / 500000, 27501 / 500000, 365013 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 233387212 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 225580510 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 240704624 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 235480491 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 232097520 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 281895537 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 273155465 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 265666030 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 255932993 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 248070577 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 242174712 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 221729419 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 231517669 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 216993650 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 212334085 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 228295689 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 215986625 / 1000000 }
            )
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 210934298 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 200962640 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 206965638 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 225417775 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 215067965 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 210812016 / 1000000 }
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
      (11049188382142920650169 / 327680000000000000000000000 : Rat) := by
  decide +kernel

end Shard386
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
