import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 193
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard193

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'right'), (2, 'left'), (5, 'left'), (4, 'left'), (2, 'right')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![1888 / 15625, 151671 / 8000000, 105003 / 8000000],
    ![253331 / 2000000, 278343 / 8000000, 35001 / 8000000],
    ![1888 / 15625, 301677 / 8000000, 105003 / 8000000],
    ![128749 / 1000000, 315009 / 16000000, 35001 / 3200000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (2 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 55478523 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 45551273 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 53169114 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 47914492 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 55767554 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 52544502 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 44607746 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![14, 15, 9, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 58589131 / 1000000 }
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 47060484 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 49525540 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![14, 15, 9, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 55186373 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 63805972 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 62674319 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 68331619 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 64303466 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 68424186 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 68889853 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 71232584 / 1000000 }
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
      (80876898979521739491843 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard193
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
