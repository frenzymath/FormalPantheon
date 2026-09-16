import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 104
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard104

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right'), (0, 'left'), (0, 'right'), (2, 'left'), (4, 'right')), 24 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![414991 / 4000000, 35001 / 8000000, 35001 / 8000000],
    ![37999 / 400000, 105003 / 8000000, 105003 / 8000000],
    ![23333 / 200000, 11667 / 1000000, 0],
    ![27187 / 250000, 105003 / 16000000, 105003 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 41199823 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 42053865 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 17980185 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 2, 14, 8]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 25243031 / 1000000 }
              )
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 25880420 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 30511646 / 1000000 }
              )
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56279915 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45779441 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 45902408 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 66397335 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 54266463 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 52381580 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 66287973 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 58333797 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 8
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 48154856 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 61706110 / 1000000 }
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 75124932 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 82857043 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 76787090 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 88641362 / 1000000 }
          )
        )
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 108805978 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 95178151 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 107201365 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 79352750 / 1000000 }
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
      (14581358273612997696951 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard104
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
