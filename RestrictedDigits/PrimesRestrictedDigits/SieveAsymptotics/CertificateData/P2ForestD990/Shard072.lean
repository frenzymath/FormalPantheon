import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 72
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard072

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'right'), (3, 'right'), (4, 'right'), (3, 'left'), (1, 'left'), (3, 'left')), 18 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![518329 / 4000000, 81669 / 8000000, 35001 / 8000000],
    ![128749 / 1000000, 315009 / 16000000, 35001 / 3200000],
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![98999 / 800000, 105003 / 8000000, 105003 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 63401945 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 57078183 / 1000000 }
          )
        )
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 55958890 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 55715390 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 57706997 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 51551504 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 61036110 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 48968771 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 43464942 / 1000000 }
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 44406206 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 41538904 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 38943730 / 1000000 }
            )
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 9, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
            upper := 45493830 / 1000000 }
        )
      )
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 46476525 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 44365206 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 40080038 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 43556316 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 39409775 / 1000000 }
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
      (2466876441096854421921 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard072
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
