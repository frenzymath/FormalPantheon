import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 227
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard227

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right'), (4, 'left'), (5, 'left'), (4, 'left'), (5, 'right'), (0, 'right')), 26 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 35001 / 2000000, 35001 / 2000000],
    ![834983 / 8000000, 585021 / 16000000, 35001 / 4000000],
    ![100831 / 1000000, 114171 / 2000000, 35001 / 8000000],
    ![27187 / 250000, 53127 / 1000000, 35001 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 9, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 35071099 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 44326012 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 44699212 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 53836273 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 65753179 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 56001210 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 70982661 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 78199028 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 81491507 / 1000000 }
            )
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 2, 14, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 48898358 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 2, 2, 14, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 59791604 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 73469992 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 62018353 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 75557590 / 1000000 }
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 2, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 49884511 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 60875084 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 63943903 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 77764092 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 2, 14, 14, 15, 9]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 75451826 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 14, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 86866822 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 88198155 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 100675287 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 98025464 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![2, 2, 2, 2, 14, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 112642794 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 119464919 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![2, 2, 2, 2, 14, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 135891339 / 1000000 }
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
      (225223634050245033631983 / 32768000000000000000000000000 : Rat) := by
  decide +kernel

end Shard227
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
