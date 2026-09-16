import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 279
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard279

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'right'), (3, 'left'), (4, 'left'), (4, 'right'), (1, 'right'), (4, 'left')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![23333 / 200000, 11667 / 1000000, 0],
    ![209579 / 2000000, 1538391 / 32000000, 105003 / 32000000],
    ![221663 / 2000000, 11667 / 800000, 35001 / 4000000],
    ![27187 / 250000, 775029 / 16000000, 35001 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 32519921 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 38213353 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 39964416 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 51882994 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 15, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56759973 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 50867486 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 8, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 28607992 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 32517511 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 31098663 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 38834111 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 2, 2, 14, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 37645910 / 1000000 }
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 14, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 17545665 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 24224582 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 25645060 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 8, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 20097218 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 2, 2, 2, 2, 14, 9]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 27601862 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 2, 2, 2, 14, 9]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 22201989 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 22014661 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 8, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 16578364 / 1000000 }
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
      (95191974706286569900437 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard279
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
