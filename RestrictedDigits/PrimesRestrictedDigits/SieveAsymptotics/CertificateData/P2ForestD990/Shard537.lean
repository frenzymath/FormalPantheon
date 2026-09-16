import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 537
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard537

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (5, 'right'), (1, 'left'), (3, 'left'), (5, 'right')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![16249 / 250000, 525021 / 8000000, 525021 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 525021 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![149993 / 2000000, 485019 / 8000000, 485019 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 30, 31]
                upper := 581052307 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 595751569 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 622645083 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 631994831 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 651509463 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 653348651 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 584533443 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 626370773 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 641817333 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 602130882 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 645194547 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 587750866 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 631817034 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 656355456 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 649628282 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 590142183 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 634444658 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 648209516 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 675580962 / 1000000 }
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
      (23590554167987942909013 / 256000000000000000000000000 : Rat) := by
  decide +kernel

end Shard537
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
