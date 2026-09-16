import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 308
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard308

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (2, 'right'), (1, 'left')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![359989 / 4000000, 35001 / 3200000, 35001 / 3200000],
    ![84997 / 1000000, 185007 / 4000000, 35001 / 4000000],
    ![37999 / 400000, 105003 / 8000000, 105003 / 8000000],
    ![100831 / 1000000, 81669 / 8000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 136581939 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.split (1 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 172257418 / 1000000 }
                )
                (.retain
                  { baseline := 8
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 171138016 / 1000000 }
                )
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 167693191 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 153478648 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 134038427 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 161549438 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 117280403 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 150749647 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 165608073 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 173063162 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 97981366 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 124979642 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 133250890 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 157549281 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 148354666 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 143143906 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 145146573 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 170078447 / 1000000 }
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
      (210639748388749413934239 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard308
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
