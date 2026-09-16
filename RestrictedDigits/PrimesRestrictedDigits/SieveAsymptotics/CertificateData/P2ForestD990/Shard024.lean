import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 24
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard024

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'left'), (0, 'left'), (4, 'right'), (0, 'right'), (1, 'right')), 22 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![269999 / 2000000, 245007 / 8000000, 245007 / 8000000],
    ![559999 / 4000000, 105003 / 3200000, 105003 / 3200000],
    ![606667 / 4000000, 431679 / 16000000, 245007 / 16000000],
    ![574999 / 4000000, 35001 / 1600000, 35001 / 1600000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
              upper := 78336917 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 14, 31, 31, 25, 1, 1]
              upper := 85993152 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 25, 17, 1, 1]
              upper := 70286953 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 25, 17, 1, 1]
                upper := 78873892 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 25, 1, 1]
                upper := 85283746 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 14, 14, 31, 31, 25, 1, 1]
            upper := 91810243 / 1000000 }
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
              upper := 90322427 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 25, 1, 1]
                upper := 94838477 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 25, 1]
                upper := 104541057 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 97930647 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 17, 1, 1]
                upper := 91943366 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
                upper := 95010845 / 1000000 }
            )
          )
        )
        (.split (3 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 1, 1, 1]
                upper := 76777866 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 25, 17, 1, 1]
                upper := 74901649 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 17, 1, 1]
                upper := 91020137 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 25, 25, 1, 1]
                upper := 94182163 / 1000000 }
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
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 100613191 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 14, 31, 31, 31, 25, 1, 1]
              upper := 106809699 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 25, 17, 1]
                upper := 99588958 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 31, 31, 31, 25, 17, 1]
                upper := 106405689 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 25, 17, 1]
                upper := 101113487 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 14, 14, 31, 31, 25, 25, 1]
                upper := 106610519 / 1000000 }
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
      (1834013129028915596751 / 163840000000000000000000000 : Rat) := by
  decide +kernel

end Shard024
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
