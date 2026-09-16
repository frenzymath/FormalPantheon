import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 208
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard208

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (3, 'left'), (3, 'left'), (2, 'left'), (4, 'left')), 25 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![221663 / 2000000, 66669 / 2000000, 35001 / 4000000],
    ![866651 / 8000000, 170673 / 3200000, 245007 / 32000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000],
    ![23333 / 200000, 98337 / 2000000, 0]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 33316634 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 21781456 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 35073019 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 39520433 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 48960307 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 42725478 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 51645743 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57812240 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 52526275 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 61006028 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 53452736 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 63275774 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 96921048 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 83901941 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 94807282 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 14, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 103977322 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 73710203 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 80855987 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 84580095 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 65770434 / 1000000 }
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 72855064 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 78984164 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 73740525 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 76900618 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 71613381 / 1000000 }
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
      (91967785694371485276273 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard208
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
