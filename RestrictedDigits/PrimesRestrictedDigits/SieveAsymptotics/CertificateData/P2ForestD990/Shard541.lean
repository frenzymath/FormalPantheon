import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 541
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard541

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (5, 'right'), (1, 'right'), (1, 'left'), (3, 'right')), 14 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![16249 / 250000, 975039 / 16000000, 975039 / 16000000],
    ![16249 / 250000, 75003 / 1000000, 225009 / 4000000],
    ![16249 / 250000, 225009 / 3200000, 975039 / 16000000],
    ![84997 / 1000000, 185007 / 4000000, 185007 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 469394970 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 506108765 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 575278522 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 541498276 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 587027151 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 625364550 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 594249798 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 559663427 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 590053616 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 625646624 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 639154604 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 673940475 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![14, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 654727134 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![14, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 673207761 / 1000000 }
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (45208613646453818628963 / 512000000000000000000000000 : Rat) := by
  decide +kernel

end Shard541
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
