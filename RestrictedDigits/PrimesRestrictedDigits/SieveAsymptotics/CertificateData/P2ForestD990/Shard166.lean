import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 166
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard166

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'right'), (2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (2, 'right')), 20 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![229997 / 2000000, 35001 / 1600000, 35001 / 1600000],
    ![1888 / 15625, 301677 / 8000000, 105003 / 8000000],
    ![229997 / 2000000, 325011 / 8000000, 35001 / 1600000],
    ![503329 / 4000000, 338343 / 16000000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 9, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
            upper := 80758479 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 84073197 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 92228670 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 95672589 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 87558770 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 82250049 / 1000000 }
            )
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 9, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
            upper := 98145591 / 1000000 }
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 100819990 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 98213210 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 97686208 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 86494758 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 88293957 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 107175659 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 110759716 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 114980393 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 111809868 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 115970404 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 108874151 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 121447598 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 115077627 / 1000000 }
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
      (140025340573727010150789 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard166
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
