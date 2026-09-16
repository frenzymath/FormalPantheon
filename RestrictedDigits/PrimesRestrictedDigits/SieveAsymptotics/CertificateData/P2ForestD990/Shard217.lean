import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 217
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard217

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (3, 'right'), (4, 'left'), (5, 'left'), (4, 'right'), (2, 'right')), 24 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![100831 / 1000000, 114171 / 2000000, 35001 / 8000000],
    ![16933 / 160000, 436683 / 8000000, 105003 / 16000000],
    ![106873 / 1000000, 28251 / 800000, 315009 / 32000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 68238238 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 67416217 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 77770670 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 14, 15, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 85117673 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 88961841 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 74427454 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 93606905 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 96890012 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 104524373 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 108495794 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 123926067 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 72131762 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 82658366 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75175183 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 85248928 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60489658 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60420026 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 76257212 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 80788603 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 83833425 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 94359755 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 108187940 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 116809462 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 129874826 / 1000000 }
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
      (63680561088196160223189 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard217
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
