import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 389
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard389

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'left'), (4, 'left'), (5, 'right'), (3, 'left'), (1, 'left')), 27 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 81003 / 1600000, 81003 / 1600000],
    ![37999 / 400000, 240009 / 4000000, 81003 / 1600000],
    ![84997 / 1000000, 26001 / 400000, 26001 / 400000],
    ![37999 / 400000, 240009 / 4000000, 240009 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 302553249 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 301169973 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 302196052 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 315768307 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 307754686 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 301049399 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 312509997 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 294151024 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 291821721 / 1000000 }
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 313171959 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 299332245 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 296941924 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 297987885 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 293098834 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 294540700 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 342277477 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 335988873 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 338335170 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 322870976 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 314366251 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 323221865 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 317086800 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 314780257 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 300866288 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 316016724 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 15, 9]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 305666754 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 15, 15, 9]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 296365576 / 1000000 }
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
      (37395020092579007522733 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard389
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
