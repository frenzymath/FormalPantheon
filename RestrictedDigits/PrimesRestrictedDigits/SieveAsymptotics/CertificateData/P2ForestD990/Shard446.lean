import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 446
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard446

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'left'), (5, 'left'), (4, 'left'), (2, 'right')), 31 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![84997 / 1000000, 185007 / 4000000, 185007 / 4000000],
    ![84997 / 1000000, 26001 / 400000, 295011 / 8000000],
    ![84997 / 1000000, 26001 / 400000, 185007 / 4000000],
    ![37999 / 400000, 81003 / 1600000, 255009 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 270824862 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 279219979 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 288626659 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.split (4 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 15
                    middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 269983858 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 15
                    middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 275481178 / 1000000 }
                )
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 290193788 / 1000000 }
              )
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 294329421 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 298714899 / 1000000 }
              )
            )
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 298649727 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 305622839 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 309127685 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 304933990 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 318222558 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 324890789 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 325721787 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 329638370 / 1000000 }
              )
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 326739059 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 352363600 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 332439578 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 331706551 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 339436662 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 348598399 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 340700308 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 356731567 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 344676821 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 323207760 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 332388244 / 1000000 }
            )
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 328109759 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 333547701 / 1000000 }
              )
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 337116859 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 352080606 / 1000000 }
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
      (97702247425710154693779 / 1024000000000000000000000000 : Rat) := by
  decide +kernel

end Shard446
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
