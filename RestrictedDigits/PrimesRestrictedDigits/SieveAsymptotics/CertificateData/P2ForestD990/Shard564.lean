import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 564
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard564

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (1, 'left'), (3, 'left'), (5, 'right'), (1, 'left'), (3, 'left')), 21 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![16249 / 250000, 825033 / 16000000, 825033 / 16000000],
    ![16249 / 250000, 975039 / 16000000, 825033 / 16000000],
    ![16249 / 250000, 225009 / 4000000, 225009 / 4000000],
    ![84997 / 1000000, 295011 / 8000000, 295011 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 489785738 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 532936306 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 573358383 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 611888683 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 627512688 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 627385682 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 642115313 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 695839998 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 649564852 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 704586521 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 726629139 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 14, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 720315377 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 715220138 / 1000000 }
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 511343903 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 593391254 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 623260421 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 702391112 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 14, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 649073467 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 650437608 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 704021486 / 1000000 }
          )
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 14, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 735175275 / 1000000 }
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (782163960714582254113059 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard564
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
