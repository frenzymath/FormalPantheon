import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 209
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard209

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (3, 'left'), (3, 'left'), (2, 'left'), (4, 'right')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![221663 / 2000000, 66669 / 2000000, 35001 / 4000000],
    ![399991 / 4000000, 460017 / 8000000, 245007 / 16000000],
    ![52499 / 500000, 27501 / 500000, 35001 / 2000000],
    ![866651 / 8000000, 170673 / 3200000, 245007 / 32000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 85458549 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 97518447 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 108001260 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 14, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 114172355 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 14, 15, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 106560171 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 86387633 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 98596752 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 109200521 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 84444609 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 80854240 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75715387 / 1000000 }
            )
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 84916823 / 1000000 }
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 97291929 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 108025398 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 9, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 82861422 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 78133754 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 74611653 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 111440493 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 112292680 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 107748396 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 101287619 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 95114464 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 88608426 / 1000000 }
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
      (34563189226001074262001 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard209
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
