import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0LeafValidatorD970
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971

/-!
# exact P0 forest shard 45
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Shard045

/- Root 1, exact path ((0, 'left'), (0, 'left')), 59 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![212499 / 1000000, 212499 / 1000000, 342491 / 4000000],
    ![212499 / 1000000, 212499 / 1000000, 16249 / 250000],
    ![16 / 75, 16 / 75, 16249 / 250000],
    ![147503 / 500000, 172497 / 1000000, 16249 / 250000]
  ]

theorem root_eq_path :
    root = ((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision Rat :=
  (.split (0 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain (25719002 / 1000000))
            (.retain (75035661 / 1000000))
          )
          (.split (1 : Fin 6)
            (.retain (26883809 / 1000000))
            (.retain (76140123 / 1000000))
          )
        )
        (.split (0 : Fin 6)
          (.retain (27385590 / 1000000))
          (.split (1 : Fin 6)
            (.retain (53366864 / 1000000))
            (.retain (101041668 / 1000000))
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain (147736576 / 1000000))
              (.retain (150768780 / 1000000))
            )
            (.retain (104899565 / 1000000))
          )
          (.split (0 : Fin 6)
            (.retain (55014415 / 1000000))
            (.retain (106173638 / 1000000))
          )
        )
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (171092303 / 1000000))
              (.retain (174503533 / 1000000))
            )
            (.retain (129983714 / 1000000))
          )
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (212310936 / 1000000))
              (.retain (216480216 / 1000000))
            )
            (.split (0 : Fin 6)
              (.retain (238845217 / 1000000))
              (.retain (276548489 / 1000000))
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain (74569535 / 1000000))
              (.retain (122349671 / 1000000))
            )
            (.split (3 : Fin 6)
              (.retain (78040918 / 1000000))
              (.retain (123730672 / 1000000))
            )
          )
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain (119575767 / 1000000))
              (.retain (164828364 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (205834446 / 1000000))
              (.retain (240684529 / 1000000))
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.split (5 : Fin 6)
              (.retain (170926552 / 1000000))
              (.retain (128328718 / 1000000))
            )
            (.split (4 : Fin 6)
              (.retain (212108351 / 1000000))
              (.retain (254870125 / 1000000))
            )
          )
          (.split (4 : Fin 6)
            (.split (1 : Fin 6)
              (.retain (227898306 / 1000000))
              (.retain (261873427 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (269132131 / 1000000))
              (.split (0 : Fin 6)
                (.retain (303541673 / 1000000))
                (.retain (297621540 / 1000000))
              )
            )
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.split (2 : Fin 6)
                (.retain (313250877 / 1000000))
                (.retain (319176158 / 1000000))
              )
              (.retain (322922569 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (270278518 / 1000000))
              (.retain (307939397 / 1000000))
            )
          )
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain (152887678 / 1000000))
              (.retain (238086910 / 1000000))
            )
            (.split (2 : Fin 6)
              (.retain (255813010 / 1000000))
              (.retain (295141926 / 1000000))
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.split (5 : Fin 6)
                (.retain (346629437 / 1000000))
                (.retain (353178431 / 1000000))
              )
              (.retain (357319201 / 1000000))
            )
            (.split (1 : Fin 6)
              (.split (5 : Fin 6)
                (.retain (362584267 / 1000000))
                (.retain (369445118 / 1000000))
              )
              (.split (2 : Fin 6)
                (.retain (374853172 / 1000000))
                (.retain (404299776 / 1000000))
              )
            )
          )
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.split (5 : Fin 6)
                (.retain (423273472 / 1000000))
                (.retain (401706660 / 1000000))
              )
              (.retain (390527396 / 1000000))
            )
            (.split (1 : Fin 6)
              (.split (5 : Fin 6)
                (.retain (437740429 / 1000000))
                (.retain (417200762 / 1000000))
              )
              (.split (2 : Fin 6)
                (.retain (461078655 / 1000000))
                (.retain (488104516 / 1000000))
              )
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ q => q) =
      (581334930794958593383937 / 9216000000000000000000000000 : Rat) := by
  decide +kernel

end Shard045
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
