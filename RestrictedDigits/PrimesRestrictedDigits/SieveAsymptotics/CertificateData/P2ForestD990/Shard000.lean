import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 0
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard000

/- Root 0, exact path ((0, 'left'), (2, 'left'), (0, 'left'), (2, 'left'), (3, 'left'), (2, 'left')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![2735011 / 16000000, 35001 / 6400000, 35001 / 6400000],
    ![156667 / 1000000, 11667 / 400000, 35001 / 2000000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![180001 / 1000000, 0, 0]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 8, 1, 1, 1, 1, 1, 1]
              upper := 5840909 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 12, 17, 1, 1, 1, 1, 1]
                upper := 6120501 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 8, 17, 1, 1, 1, 1, 1]
                upper := 8007335 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
              upper := 16204139 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 11913765 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 12708610 / 1000000 }
            )
          )
        )
      )
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
            upper := 15437377 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 9225016 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 11124830 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
              upper := 16553253 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
              upper := 19103062 / 1000000 }
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 13663370 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 11768976 / 1000000 }
            )
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
            upper := 22811123 / 1000000 }
        )
      )
      (.retain
        { baseline := 1
          legacy := 1
          middle := ![1, 1, 1, 1, 1, 1, 1, 1]
          inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
          upper := 33890173 / 1000000 }
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (1953821382779630751057 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard000
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
