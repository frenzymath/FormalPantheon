import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 27
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard027

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'left'), (0, 'right'), (1, 'left'), (5, 'right'), (3, 'left')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![293333 / 2000000, 198339 / 8000000, 105003 / 8000000],
    ![606667 / 4000000, 431679 / 16000000, 245007 / 16000000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![621667 / 4000000, 128337 / 8000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 25, 1, 1, 1]
                upper := 20713577 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 12, 25, 1, 1, 1]
                upper := 26049537 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 8, 17, 1, 1, 1]
                upper := 22953414 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 8, 1, 1, 1, 1]
                upper := 18744789 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
                upper := 37325199 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 25, 17, 1, 1, 1]
                upper := 29533275 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 25, 17, 1, 1, 1]
              upper := 29266203 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
                upper := 15139421 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 8, 17, 1, 1, 1, 1]
                upper := 10989852 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 25, 1, 1, 1, 1]
              upper := 18107822 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 25, 17, 1, 1, 1]
            upper := 28602120 / 1000000 }
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 25, 1, 1, 1]
                upper := 24523883 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 25, 1, 1, 1]
                upper := 29918462 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 25, 1, 1, 1]
              upper := 28423487 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 25, 1, 1, 1]
              upper := 29100416 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 25, 17, 1, 1]
              upper := 38975181 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
              upper := 42616213 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
              upper := 41371317 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 25, 1, 1, 1]
                upper := 37659210 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 25, 1, 1, 1]
                upper := 37970853 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 25, 1, 1, 1]
                upper := 43038660 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 25, 17, 1, 1]
                upper := 43342052 / 1000000 }
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
      (1515391357024083813219 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard027
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
