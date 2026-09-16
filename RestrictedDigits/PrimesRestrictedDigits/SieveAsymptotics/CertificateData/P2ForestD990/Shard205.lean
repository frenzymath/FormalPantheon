import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 205
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard205

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'right'), (2, 'right'), (2, 'right'), (0, 'left'), (3, 'right')), 26 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![221663 / 2000000, 66669 / 2000000, 35001 / 4000000],
    ![23333 / 200000, 98337 / 2000000, 0],
    ![221663 / 2000000, 208341 / 4000000, 35001 / 4000000],
    ![22583 / 200000, 11667 / 640000, 245007 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (1 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 99638385 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 15, 15, 9, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 91947908 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 81430711 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 75071289 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 14, 14, 15, 9, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 65945931 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 97257955 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 81679861 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75289747 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 66045554 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 92599236 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 79701122 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 74183477 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75627717 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 47894031 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 40495366 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 46355263 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 30672278 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 28683473 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 14, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 35355142 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 14, 14, 15, 9, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 40173670 / 1000000 }
              )
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56904827 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 50817001 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 2, 14, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 54415999 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 14, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 58393258 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 14, 9, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 55786809 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 14, 14, 15, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 66700028 / 1000000 }
              )
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
      (88750261239126603046047 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard205
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
