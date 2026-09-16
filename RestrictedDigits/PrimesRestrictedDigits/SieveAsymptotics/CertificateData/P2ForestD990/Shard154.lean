import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 154
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard154

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'right'), (2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (3, 'right')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![68333 / 500000, 612 / 15625, 35001 / 4000000],
    ![52333 / 400000, 10467 / 320000, 35001 / 2000000],
    ![543331 / 4000000, 81669 / 3200000, 315009 / 16000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 25]
              upper := 66832658 / 1000000 }
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 25]
                upper := 65683905 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 25]
                upper := 67227838 / 1000000 }
            )
          )
        )
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 25]
                upper := 62611651 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 25]
                upper := 60555832 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 25]
              upper := 63214871 / 1000000 }
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 14, 31, 25]
              upper := 55413690 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 50052815 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 59954533 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 51467344 / 1000000 }
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
            upper := 53124105 / 1000000 }
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
            upper := 44650738 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
            upper := 53513544 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 47061971 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
              upper := 43433162 / 1000000 }
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
      (39247440986710508052339 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard154
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
