import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0LeafValidatorD970
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971

/-!
# exact P0 forest shard 27
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Shard027

/- Root 0, exact path ((1, 'right'), (0, 'left'), (3, 'right'), (0, 'right'), (2, 'left'), (4, 'right')), 60 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![101501 / 400000, 96249 / 500000, 342491 / 4000000],
    ![212499 / 1000000, 212499 / 1000000, 342491 / 4000000],
    ![932503 / 4000000, 767489 / 4000000, 342491 / 4000000],
    ![101501 / 400000, 96249 / 500000, 24099 / 320000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision Rat :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain (366778600 / 1000000))
              (.retain (396440975 / 1000000))
            )
            (.split (0 : Fin 6)
              (.retain (401196335 / 1000000))
              (.retain (411476487 / 1000000))
            )
          )
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (409702909 / 1000000))
              (.retain (423353024 / 1000000))
            )
            (.split (0 : Fin 6)
              (.retain (428145968 / 1000000))
              (.retain (424535618 / 1000000))
            )
          )
        )
        (.split (5 : Fin 6)
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain (458295263 / 1000000))
              (.retain (443871900 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (456343516 / 1000000))
              (.retain (438248411 / 1000000))
            )
          )
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain (503899378 / 1000000))
              (.retain (477468433 / 1000000))
            )
            (.split (0 : Fin 6)
              (.retain (461869002 / 1000000))
              (.retain (457952689 / 1000000))
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (5 : Fin 6)
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (448085515 / 1000000))
              (.retain (451940636 / 1000000))
            )
            (.split (2 : Fin 6)
              (.retain (452341443 / 1000000))
              (.retain (464256908 / 1000000))
            )
          )
          (.split (3 : Fin 6)
            (.retain (497758315 / 1000000))
            (.split (0 : Fin 6)
              (.retain (467539411 / 1000000))
              (.retain (475471912 / 1000000))
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (454669421 / 1000000))
              (.retain (466313097 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (500234035 / 1000000))
              (.retain (480067585 / 1000000))
            )
          )
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.retain (489313108 / 1000000))
              (.retain (509364796 / 1000000))
            )
            (.split (0 : Fin 6)
              (.retain (484990951 / 1000000))
              (.retain (491914666 / 1000000))
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (468784489 / 1000000))
              (.retain (481385042 / 1000000))
            )
            (.split (3 : Fin 6)
              (.retain (508177800 / 1000000))
              (.retain (494435613 / 1000000))
            )
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain (510735404 / 1000000))
              (.retain (497204104 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (514055219 / 1000000))
              (.retain (507187718 / 1000000))
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain (512490255 / 1000000))
              (.retain (525875863 / 1000000))
            )
            (.split (1 : Fin 6)
              (.retain (529035907 / 1000000))
              (.retain (521990030 / 1000000))
            )
          )
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (517966560 / 1000000))
              (.retain (529959625 / 1000000))
            )
            (.split (2 : Fin 6)
              (.retain (515106125 / 1000000))
              (.retain (521243138 / 1000000))
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (2 : Fin 6)
              (.retain (466504227 / 1000000))
              (.retain (474405827 / 1000000))
            )
            (.retain (496645878 / 1000000))
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              (.retain (511587563 / 1000000))
              (.retain (504720063 / 1000000))
            )
            (.retain (496841442 / 1000000))
          )
        )
        (.split (1 : Fin 6)
          (.split (4 : Fin 6)
            (.retain (507038881 / 1000000))
            (.split (3 : Fin 6)
              (.retain (521556687 / 1000000))
              (.retain (514510810 / 1000000))
            )
          )
          (.split (0 : Fin 6)
            (.split (4 : Fin 6)
              (.retain (497924457 / 1000000))
              (.retain (508777511 / 1000000))
            )
            (.split (2 : Fin 6)
              (.retain (495811400 / 1000000))
              (.retain (502339400 / 1000000))
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
      (593095918792361984327563 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard027
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
