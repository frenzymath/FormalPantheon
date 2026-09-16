import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 97
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard097

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right'), (0, 'left'), (0, 'left'), (2, 'left'), (2, 'right'), (3, 'left')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![27187 / 250000, 105003 / 16000000, 105003 / 16000000],
    ![221663 / 2000000, 11667 / 800000, 35001 / 4000000],
    ![23333 / 200000, 11667 / 1000000, 0],
    ![462493 / 4000000, 105003 / 32000000, 105003 / 32000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 25535663 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 20984560 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 2, 2, 14, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 29890145 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 45925913 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 60562448 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 2, 2, 14, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 40229686 / 1000000 }
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 47190311 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 63405126 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 42945699 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 49400643 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56537635 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 71356146 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 63933953 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 58298670 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57624505 / 1000000 }
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
      (4610494225132513567641 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard097
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
