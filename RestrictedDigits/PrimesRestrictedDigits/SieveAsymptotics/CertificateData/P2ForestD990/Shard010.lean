import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 10
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard010

/- Root 0, exact path ((0, 'left'), (2, 'left'), (0, 'right'), (2, 'left'), (4, 'right'), (3, 'left')), 12 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![645001 / 4000000, 35001 / 8000000, 35001 / 8000000],
    ![249667 / 1600000, 361677 / 16000000, 35001 / 3200000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![1295003 / 8000000, 35001 / 3200000, 35001 / 3200000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
              upper := 23062793 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 8, 17, 1, 1, 1, 1]
                upper := 19795027 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
                upper := 17380154 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 8, 1, 1, 1, 1, 1]
              upper := 12463317 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 8, 17, 1, 1, 1, 1]
              upper := 10731557 / 1000000 }
          )
        )
      )
      (.retain
        { baseline := 1
          legacy := 1
          middle := ![1, 1, 1, 1, 1, 1, 1, 1]
          inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
          upper := 25525982 / 1000000 }
      )
    )
    (.split (2 : Fin 6)
      (.retain
        { baseline := 1
          legacy := 1
          middle := ![1, 1, 1, 1, 1, 1, 1, 1]
          inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
          upper := 27194660 / 1000000 }
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
            upper := 24605624 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
                upper := 21115390 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 8, 1, 1, 1, 1]
                upper := 20528232 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 8, 1, 1, 1, 1]
                upper := 17439217 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 8, 17, 1, 1, 1]
                upper := 19227171 / 1000000 }
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
      (2279862867180257976573 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard010
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
