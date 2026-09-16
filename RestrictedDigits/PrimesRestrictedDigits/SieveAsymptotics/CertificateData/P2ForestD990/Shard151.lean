import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 151
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard151

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'right'), (2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'left')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![113333 / 800000, 361677 / 16000000, 35001 / 3200000],
    ![68333 / 500000, 612 / 15625, 35001 / 4000000],
    ![543331 / 4000000, 81669 / 3200000, 315009 / 16000000],
    ![293333 / 2000000, 198339 / 8000000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 25, 17, 1]
                upper := 50886804 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 25, 17, 1]
                upper := 51842721 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 25, 17, 1]
                upper := 46186707 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 25, 1]
                upper := 51701908 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 1]
              upper := 45360442 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 25, 1]
              upper := 49734062 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 14, 14, 31, 25, 1]
            upper := 53522548 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
              upper := 61770983 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 1]
              upper := 51954725 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
            upper := 48747128 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
              upper := 62807208 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
              upper := 53153436 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
            upper := 43641894 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 25, 17]
              upper := 45645416 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 25, 1]
              upper := 39783179 / 1000000 }
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
      (36276654784865998822209 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard151
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
