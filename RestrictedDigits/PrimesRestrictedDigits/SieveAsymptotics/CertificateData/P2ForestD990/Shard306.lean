import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 306
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard306

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (2, 'left'), (4, 'left'), (5, 'right')), 16 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![100831 / 1000000, 81669 / 8000000, 35001 / 8000000],
    ![100831 / 1000000, 9267 / 320000, 35001 / 8000000],
    ![37999 / 400000, 105003 / 8000000, 105003 / 8000000],
    ![16933 / 160000, 198339 / 16000000, 105003 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 94169972 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 121565477 / 1000000 }
        )
      )
      (.retain
        { baseline := 9
          legacy := 14
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 76470757 / 1000000 }
      )
    )
    (.split (2 : Fin 6)
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 104760583 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 72697088 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 107084967 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 78496704 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 79699951 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 107332552 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 101397745 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 73647270 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75258743 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 131988037 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 99592143 / 1000000 }
              )
            )
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 99623233 / 1000000 }
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 76010836 / 1000000 }
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
      (4135706371462114739871 / 256000000000000000000000000 : Rat) := by
  decide +kernel

end Shard306
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
