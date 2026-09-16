import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 578
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard578

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (1, 'right'), (2, 'left'), (4, 'right'), (4, 'left'), (1, 'right')), 13 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![84997 / 1000000, 27501 / 1000000, 27501 / 1000000],
    ![149993 / 2000000, 485019 / 8000000, 26001 / 800000],
    ![149993 / 2000000, 595023 / 16000000, 595023 / 16000000],
    ![84997 / 1000000, 185007 / 4000000, 27501 / 1000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 365595775 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 373604273 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 404282561 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 395519241 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 394291864 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 418869647 / 1000000 }
          )
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 14, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 390302201 / 1000000 }
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 14, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 457181233 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 490160100 / 1000000 }
          )
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 14, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 445254694 / 1000000 }
        )
      )
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 2, 2, 2, 14, 14, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 426594047 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 477501097 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 2, 2, 2, 14, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 439033982 / 1000000 }
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
      (252795672718569843994971 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard578
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
