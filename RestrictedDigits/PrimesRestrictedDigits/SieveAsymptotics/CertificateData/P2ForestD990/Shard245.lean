import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 245
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard245

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'left')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![284999 / 2000000, 35001 / 2000000, 0],
    ![518329 / 4000000, 341679 / 8000000, 0],
    ![253331 / 2000000, 278343 / 8000000, 35001 / 8000000],
    ![284999 / 2000000, 29001 / 800000, 0]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 8, 16]
              upper := 2156367 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 12, 0]
              upper := 2182325 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
            upper := 3998583 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 8]
              upper := 3470446 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 6212786 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 1229182 / 1000000 }
            )
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 8]
            upper := 2488083 / 1000000 }
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 11071027 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 11040254 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 7496223 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 15017988 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 11095634 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 7683269 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 6206519 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![8, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 3696789 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 7691093 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 10]
                upper := 6457537 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 8]
              upper := 3610924 / 1000000 }
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
      (8183264777757927555687 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard245
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
