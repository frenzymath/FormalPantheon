import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 387
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard387

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left')), 23 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![399991 / 4000000, 192507 / 4000000, 192507 / 4000000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![37999 / 400000, 240009 / 4000000, 240009 / 4000000],
    ![52499 / 500000, 365013 / 8000000, 365013 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 242164639 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 249629744 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 236559095 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 245126928 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 247136411 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 9, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 251956546 / 1000000 }
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
                middle := ![15, 15, 15, 15, 15, 9, 9, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 273314405 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                  upper := 286813972 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                  upper := 279260169 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 263495822 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 260345149 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 263175330 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 9, 9, 1]
                  inverse := ![2, 2, 2, 14, 30, 31, 31, 31]
                  upper := 256127908 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                  inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                  upper := 258092222 / 1000000 }
              )
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 222545842 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 226647910 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 216500601 / 1000000 }
          )
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 210153202 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 205908832 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 228712985 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 232849200 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 236783002 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 241538812 / 1000000 }
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
      (578768130554867394961779 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard387
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
