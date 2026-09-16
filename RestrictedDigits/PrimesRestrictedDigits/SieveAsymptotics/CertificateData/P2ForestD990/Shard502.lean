import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 502
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard502

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'right'), (4, 'left'), (4, 'right'), (0, 'left'), (4, 'left'), (4, 'left'), (2, 'right')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 82503 / 2000000, 105003 / 8000000],
    ![739979 / 8000000, 980037 / 16000000, 385011 / 32000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 2000000],
    ![37999 / 400000, 81003 / 1600000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 181114261 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 203862997 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 160749026 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 224892963 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 177032364 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 158109328 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 2, 2, 14]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 161587475 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 226688976 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 183075107 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 359950038 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 458669591 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 2, 2, 2, 2, 2, 14, 14]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 392317660 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 301514115 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 248835245 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 277672402 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 226407559 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 232233623 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 2, 14]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 182256728 / 1000000 }
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
      (55654153898660575883559 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard502
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
