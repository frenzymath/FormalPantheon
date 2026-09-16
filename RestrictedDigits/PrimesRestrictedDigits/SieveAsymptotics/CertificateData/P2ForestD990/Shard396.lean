import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 396
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard396

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'left'), (1, 'right'), (4, 'right')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 29001 / 800000, 29001 / 800000],
    ![37999 / 400000, 240009 / 4000000, 82503 / 2000000],
    ![37999 / 400000, 81003 / 1600000, 81003 / 1600000],
    ![399991 / 4000000, 460017 / 8000000, 310011 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 236661047 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 241869542 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 249234229 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 246995819 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 261458624 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
              upper := 272605965 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 258513046 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 256194034 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 235906409 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 231123401 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 224649828 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 221950588 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 245879902 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 238887855 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 240400516 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 234552655 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 226651985 / 1000000 }
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
      (291492305168548162343157 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard396
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
