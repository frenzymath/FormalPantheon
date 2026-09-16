import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 250
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard250

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'right'), (4, 'right')), 19 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![253331 / 2000000, 128337 / 8000000, 35001 / 8000000],
    ![23333 / 200000, 98337 / 2000000, 0],
    ![253331 / 2000000, 278343 / 8000000, 35001 / 8000000],
    ![518329 / 4000000, 66669 / 2000000, 0]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 8, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 9831201 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 8, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 12313022 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 14, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 13783168 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 17613951 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 18209336 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![14, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 19125169 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 19758865 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 17979803 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 8, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 15954907 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 12, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 7336570 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 14, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 12353466 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 14, 8, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 11886401 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![2, 2, 8, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 9906142 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 10763341 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 11911716 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 14, 8, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 7501674 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![2, 2, 2, 8, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 5779115 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 8, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 12438526 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![2, 2, 14, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 16033931 / 1000000 }
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
      (992505454422404911929 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard250
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
