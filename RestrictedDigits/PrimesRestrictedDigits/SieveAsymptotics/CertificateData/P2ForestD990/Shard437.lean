import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 437
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard437

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'right'), (3, 'right'), (3, 'left'), (1, 'left'), (3, 'right')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 82503 / 2000000, 255009 / 8000000],
    ![37999 / 400000, 240009 / 4000000, 255009 / 8000000],
    ![359989 / 4000000, 500019 / 8000000, 625023 / 16000000],
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
            upper := 278897620 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 277548951 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 275981291 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 271462658 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 255974299 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 258790768 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 262715520 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 258419997 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 271319010 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 277792097 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 274259299 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 260290440 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 260139033 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 252006460 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 271760613 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 263454056 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 263683352 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 267387174 / 1000000 }
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
      (12816501887929481156871 / 327680000000000000000000000 : Rat) := by
  decide +kernel

end Shard437
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
