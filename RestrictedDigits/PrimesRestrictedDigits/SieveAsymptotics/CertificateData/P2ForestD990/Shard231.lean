import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 231
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard231

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'left'), (5, 'right'), (0, 'left')), 30 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![391657 / 4000000, 63669 / 1600000, 35001 / 4000000],
    ![181661 / 2000000, 248343 / 4000000, 0],
    ![84997 / 1000000, 26001 / 400000, 35001 / 4000000],
    ![100831 / 1000000, 114171 / 2000000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 1
                    legacy := 9
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 50790586 / 1000000 }
                )
                (.retain
                  { baseline := 1
                    legacy := 9
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 58905036 / 1000000 }
                )
              )
              (.retain
                { baseline := 1
                  legacy := 8
                  middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 54267936 / 1000000 }
              )
            )
            (.split (5 : Fin 6)
              (.split (2 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 68605842 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 14]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 72476159 / 1000000 }
                )
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 66108897 / 1000000 }
              )
            )
          )
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 50159676 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 63862330 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 54772200 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57498755 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 74803233 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 76473784 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 81341820 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 83747388 / 1000000 }
              )
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 92140529 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 89352448 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 90285837 / 1000000 }
              )
            )
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 69895737 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 87651809 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 39318947 / 1000000 }
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 64334220 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 67274280 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 93199306 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 77863033 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 69365840 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 85892176 / 1000000 }
              )
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 72925047 / 1000000 }
              )
              (.retain
                { baseline := 8
                  legacy := 14
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 59240848 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 70926752 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 79049745 / 1000000 }
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
      (394447898438291619844281 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard231
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
