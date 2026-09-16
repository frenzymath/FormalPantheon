import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 3
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard003

/- Root 0, exact path ((0, 'left'), (2, 'left'), (0, 'left'), (2, 'left'), (3, 'right'), (4, 'right')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![1295003 / 8000000, 35001 / 3200000, 35001 / 3200000],
    ![29 / 200, 35001 / 1000000, 35001 / 1000000],
    ![156667 / 1000000, 11667 / 400000, 35001 / 2000000],
    ![325001 / 2000000, 35001 / 2000000, 35001 / 2000000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 25, 17, 1, 1, 1, 1]
              upper := 66056447 / 1000000 }
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 25, 25, 1, 1, 1, 1]
                upper := 72002070 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
                upper := 75246200 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
              upper := 77323508 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
              upper := 91839563 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
              upper := 71200823 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
              upper := 77972776 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![14, 31, 31, 25, 1, 1, 1, 1]
            upper := 89538151 / 1000000 }
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 25, 17, 1, 1, 1, 1]
                upper := 62866686 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 31, 25, 1, 1, 1, 1, 1]
                upper := 59512682 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 25, 1, 1, 1, 1, 1]
                upper := 55226984 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![14, 14, 25, 25, 1, 1, 1, 1]
                upper := 60442736 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![14, 14, 31, 25, 1, 1, 1, 1]
              upper := 67034922 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 61326825 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
            upper := 57453593 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 57224197 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 25, 1, 1, 1, 1]
              upper := 52543742 / 1000000 }
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
      (347262064858249681833 / 20480000000000000000000000 : Rat) := by
  decide +kernel

end Shard003
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
