import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 140
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard140

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (4, 'right'), (3, 'left')), 16 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![95999 / 800000, 380013 / 8000000, 385011 / 16000000],
    ![124999 / 1000000, 90003 / 2000000, 105003 / 4000000],
    ![503329 / 4000000, 356679 / 8000000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 84608307 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 85937928 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 96714501 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 80102631 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 84132907 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 91126389 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 9, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 98054435 / 1000000 }
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
            upper := 98809319 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 97293676 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 104159042 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 105453224 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 97571992 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 104005115 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 95253070 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 100853877 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
              upper := 102211424 / 1000000 }
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
      (27540115921344356322021 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard140
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
