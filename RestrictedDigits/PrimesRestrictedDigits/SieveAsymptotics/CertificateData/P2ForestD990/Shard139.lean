import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 139
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard139

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (4, 'left'), (3, 'right')), 12 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000],
    ![503329 / 4000000, 356679 / 8000000, 245007 / 16000000],
    ![40133 / 320000, 716691 / 16000000, 665019 / 32000000],
    ![68333 / 500000, 612 / 15625, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 48528077 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 57038217 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 25]
              upper := 62162234 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 69095786 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 60807551 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 68396265 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 68400179 / 1000000 }
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (0 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 74564248 / 1000000 }
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 82237679 / 1000000 }
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![9, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 79982252 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 84957733 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 97302683 / 1000000 }
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
      (26193460685542064375139 / 2048000000000000000000000000 : Rat) := by
  decide +kernel

end Shard139
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
