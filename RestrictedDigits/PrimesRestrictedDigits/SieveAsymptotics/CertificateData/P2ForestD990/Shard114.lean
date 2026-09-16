import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 114
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard114

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'left'), (4, 'right')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![559999 / 4000000, 105003 / 3200000, 105003 / 3200000],
    ![269999 / 2000000, 32001 / 800000, 245007 / 8000000],
    ![29 / 200, 35001 / 1000000, 35001 / 1000000],
    ![606667 / 4000000, 253341 / 8000000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
                upper := 75625208 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
                upper := 82097050 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
                upper := 90283345 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 17, 1, 1]
                upper := 97054916 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
                upper := 97668211 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
                upper := 99562045 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 14, 31, 31, 25, 17, 1, 1]
              upper := 106056526 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 31, 31, 25, 1, 1, 1]
                upper := 104741806 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 31, 31, 25, 1, 1, 1]
                upper := 111654018 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 31, 25, 1, 1, 1]
              upper := 114968215 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 31, 25, 1, 1, 1]
              upper := 106862443 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 31, 31, 25, 1, 1, 1]
                upper := 113532544 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 31, 31, 25, 17, 1, 1]
                upper := 114610687 / 1000000 }
            )
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 25, 1, 1, 1]
              upper := 76918799 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 25, 17, 1, 1]
              upper := 92079300 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 14, 31, 31, 25, 1, 1, 1]
              upper := 100430016 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 14, 31, 31, 25, 17, 1, 1]
              upper := 100127631 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 17, 1, 1]
                upper := 108938717 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 31, 31, 25, 25, 1, 1]
                upper := 108138821 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 107607312 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 102971656 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 109188368 / 1000000 }
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
      (1464160581691395702651 / 81920000000000000000000000 : Rat) := by
  decide +kernel

end Shard114
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
