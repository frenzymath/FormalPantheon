import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 125
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard125

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (1, 'right'), (2, 'right'), (1, 'left'), (4, 'left')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![519997 / 4000000, 455013 / 16000000, 455013 / 16000000],
    ![543331 / 4000000, 558351 / 16000000, 315009 / 16000000],
    ![269999 / 2000000, 245007 / 8000000, 245007 / 8000000],
    ![293333 / 2000000, 198339 / 8000000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 25, 1, 1]
              upper := 63122229 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 25, 25, 1]
                upper := 72037650 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 25, 1]
                upper := 70656937 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 1]
                upper := 75886457 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 25, 1]
                upper := 73577572 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 25, 1]
              upper := 72402052 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 25, 1]
              upper := 96213915 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 1]
                upper := 88979870 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 1]
                upper := 86711829 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 25, 1]
              upper := 83493274 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 25, 1]
              upper := 80334418 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 1]
                upper := 90611864 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 17]
                upper := 100423748 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 25, 17]
              upper := 103941587 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 25, 1]
              upper := 84227862 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 25, 17]
              upper := 94916524 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 25, 17]
                upper := 90275308 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
                upper := 99876995 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 25, 17]
              upper := 85203244 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 25, 25]
                upper := 92645010 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
                upper := 95392751 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 25]
              upper := 101816573 / 1000000 }
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
      (125169859465720992820143 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard125
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
