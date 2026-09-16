import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 20
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard020

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'left'), (0, 'left'), (4, 'left'), (5, 'right'), (1, 'right')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![269999 / 2000000, 245007 / 8000000, 245007 / 8000000],
    ![574999 / 4000000, 35001 / 1600000, 35001 / 1600000],
    ![606667 / 4000000, 431679 / 16000000, 245007 / 16000000],
    ![621667 / 4000000, 128337 / 8000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 25, 17, 1, 1]
              upper := 34322170 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 25, 17, 1, 1]
                upper := 42595350 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 25, 1, 1]
                upper := 50624367 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 25, 17, 1, 1]
                upper := 47644015 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 25, 1, 1]
                upper := 56014238 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 25, 1, 1]
                upper := 58624338 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 67057835 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
              upper := 51386420 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 17, 1, 1]
                upper := 53760010 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 25, 25, 1, 1]
                upper := 58630033 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
                upper := 58377907 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 25, 1, 1]
                upper := 64752536 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 68158106 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 67242088 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 70168550 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 25, 1, 1]
                upper := 68518030 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 25, 17, 1, 1]
              upper := 66030153 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
              upper := 73148985 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
              upper := 74045870 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
            upper := 78920912 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
              upper := 85988536 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 90509228 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 25, 1]
                upper := 99951335 / 1000000 }
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
      (3300181599629781954549 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard020
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
