import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 364
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard364

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (2, 'right'), (2, 'right')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 29001 / 800000, 29001 / 800000],
    ![229997 / 2000000, 325011 / 8000000, 35001 / 1600000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![439993 / 4000000, 270009 / 8000000, 270009 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 177840191 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 167502724 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 15, 9, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 164718529 / 1000000 }
        )
      )
      (.split (4 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 15, 9, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 158007610 / 1000000 }
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 145925820 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 136430477 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 143821572 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 181763540 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 186523930 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 188369274 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 184178558 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 175081557 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 181030855 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 178516076 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 182477332 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 188968222 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 198054235 / 1000000 }
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
      (206381299649515178867793 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard364
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
