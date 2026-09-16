import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 278
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard278

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'right'), (3, 'left'), (4, 'left'), (4, 'right'), (1, 'left'), (3, 'right')), 25 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![221663 / 2000000, 11667 / 800000, 35001 / 4000000],
    ![100831 / 1000000, 381681 / 8000000, 35001 / 8000000],
    ![205829 / 2000000, 104337 / 3200000, 35001 / 3200000],
    ![27187 / 250000, 775029 / 16000000, 35001 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 38130941 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 43806426 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 42689204 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 39359245 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 51129690 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 54429139 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 55857871 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 61629550 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 69971196 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 58365517 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 74920590 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 84679947 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 78769118 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 67054861 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 72092133 / 1000000 }
              )
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 73131676 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 66345388 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 53086617 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 55539284 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 58617234 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![2, 2, 2, 2, 2, 2, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 68175869 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 66892792 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 83754277 / 1000000 }
            )
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 74885876 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 81466134 / 1000000 }
              )
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
      (36474553261510430201829 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard278
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
