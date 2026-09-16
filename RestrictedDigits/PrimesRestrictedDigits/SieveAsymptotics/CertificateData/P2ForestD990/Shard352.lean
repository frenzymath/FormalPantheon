import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 352
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard352

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'right'), (0, 'right')), 32 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![229997 / 2000000, 325011 / 8000000, 35001 / 1600000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![229997 / 2000000, 200007 / 4000000, 35001 / 1600000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 127139702 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 118470525 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 121894577 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 126581147 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 135416903 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 137729465 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 164340278 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 156985144 / 1000000 }
              )
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 9, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                  upper := 151119743 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                  upper := 142582961 / 1000000 }
              )
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 139833540 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 131139611 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 164127274 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 152614750 / 1000000 }
            )
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 147463525 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 141702702 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 121015119 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 115879759 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 132713838 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 130372688 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 126218403 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 114184011 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 117550645 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 117231431 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 112507481 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 112696463 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 114285451 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 122206762 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 122496919 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 114483073 / 1000000 }
            )
            (.split (2 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 114700738 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                  upper := 115057338 / 1000000 }
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
      (38510288389856037352599 / 1024000000000000000000000000 : Rat) := by
  decide +kernel

end Shard352
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
