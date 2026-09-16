import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 73
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard073

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'right'), (3, 'left'), (1, 'left'), (3, 'right')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![518329 / 4000000, 81669 / 8000000, 35001 / 8000000],
    ![1888 / 15625, 151671 / 8000000, 105003 / 8000000],
    ![128749 / 1000000, 315009 / 16000000, 35001 / 3200000],
    ![98999 / 800000, 105003 / 8000000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 68488848 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 56346818 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![14, 15, 9, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
            upper := 57710015 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 64832281 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 52685208 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 63010632 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 51265251 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 42416952 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![14, 15, 15, 9, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 72337502 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 64384902 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 67303977 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 67548934 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 60815765 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 58366275 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 45054387 / 1000000 }
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
      (1209113812419428620881 / 327680000000000000000000000 : Rat) := by
  decide +kernel

end Shard073
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
