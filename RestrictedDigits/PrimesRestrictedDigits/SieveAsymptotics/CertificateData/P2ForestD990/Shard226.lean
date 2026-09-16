import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 226
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard226

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'left'), (5, 'left'), (4, 'left'), (5, 'right'), (0, 'left')), 21 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![834983 / 8000000, 585021 / 16000000, 35001 / 4000000],
    ![414991 / 4000000, 445017 / 8000000, 0],
    ![100831 / 1000000, 114171 / 2000000, 35001 / 8000000],
    ![27187 / 250000, 53127 / 1000000, 35001 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 30931467 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 12, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 29097662 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 30439979 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 39509754 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 37549956 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 13]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60245181 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 24670745 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 30357113 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 15558117 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 24601091 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 34254796 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45920267 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 57531297 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 31927225 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 37528120 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 26616278 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![2, 2, 2, 2, 2, 2, 14, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 31481266 / 1000000 }
        )
      )
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 44317925 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 54166727 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 49169335 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56071511 / 1000000 }
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
      (11040551140694038178427 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard226
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
