import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 606
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard606

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (4, 'right'), (3, 'right'), (4, 'left'), (2, 'right'), (0, 'left')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![619973 / 8000000, 1225047 / 32000000, 775029 / 32000000],
    ![359989 / 4000000, 625023 / 16000000, 35001 / 3200000],
    ![149993 / 2000000, 485019 / 8000000, 185007 / 8000000],
    ![319987 / 4000000, 555021 / 16000000, 81003 / 3200000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (0 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 14
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 351591983 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 358202223 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 330933139 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 387716285 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 381083685 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 387704714 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 384957808 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 395944492 / 1000000 }
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 320097611 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 279284107 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 274611659 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 317363639 / 1000000 }
            )
          )
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 239828526 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 359552685 / 1000000 }
            )
            (.retain
              { baseline := 8
                legacy := 14
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 327903812 / 1000000 }
            )
          )
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 353611817 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 255732433 / 1000000 }
          )
          (.retain
            { baseline := 8
              legacy := 14
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 322666042 / 1000000 }
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
      (401318036472677096379573 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard606
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
