import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 8
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard008

/- Root 0, exact path ((0, 'left'), (2, 'left'), (0, 'right'), (2, 'left'), (4, 'left'), (2, 'left')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![273001 / 1600000, 35001 / 16000000, 35001 / 16000000],
    ![1295003 / 8000000, 35001 / 3200000, 35001 / 3200000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![180001 / 1000000, 0, 0]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 8, 17, 1, 1, 1, 1, 1]
                upper := 3850708 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
                upper := 3468683 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 8, 17, 1, 1, 1, 1, 1]
                upper := 4527553 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 10, 25, 1, 1, 1, 1, 1]
                upper := 6510089 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
              upper := 9309776 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
                upper := 4743511 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 9209868 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
              upper := 14955406 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
              upper := 10306066 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
                upper := 16792837 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 12, 25, 1, 1, 1, 1]
                  upper := 30965383 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 14, 8, 17, 1, 1, 1, 1]
                  upper := 24108215 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 8, 1, 1, 1, 1, 1]
              upper := 13070817 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.retain
        { baseline := 1
          legacy := 1
          middle := ![1, 1, 1, 1, 1, 1, 1, 1]
          inverse := ![2, 2, 8, 1, 1, 1, 1, 1]
          upper := 7775838 / 1000000 }
      )
      (.split (3 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 8, 1, 1, 1, 1, 1]
            upper := 11479173 / 1000000 }
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 8, 17, 1, 1, 1, 1]
              upper := 18781540 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
                upper := 28428176 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 8, 17, 1, 1, 1, 1]
                upper := 19573917 / 1000000 }
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
      (1144686188096121787083 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard008
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
