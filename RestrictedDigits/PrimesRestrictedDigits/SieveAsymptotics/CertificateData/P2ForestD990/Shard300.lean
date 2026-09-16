import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 300
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard300

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'right'), (4, 'right')), 13 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![399991 / 4000000, 245007 / 16000000, 245007 / 16000000],
    ![37999 / 400000, 255009 / 8000000, 105003 / 8000000],
    ![399991 / 4000000, 395013 / 16000000, 245007 / 16000000],
    ![16933 / 160000, 69669 / 3200000, 105003 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 103421627 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 111696823 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 127894028 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 135956836 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 148613652 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 151261315 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 153171558 / 1000000 }
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 102573542 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 107219024 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 124970619 / 1000000 }
          )
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 141803142 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 2, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 150223966 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 14, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 153816667 / 1000000 }
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (101750391206218364344191 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard300
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
