import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 362
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard362

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (2, 'left'), (5, 'right')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![229997 / 2000000, 31251 / 1000000, 31251 / 1000000],
    ![229997 / 2000000, 325011 / 8000000, 35001 / 1600000],
    ![52499 / 500000, 27501 / 500000, 29001 / 800000],
    ![229997 / 2000000, 325011 / 8000000, 31251 / 1000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 9, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 154074739 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 168836024 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 161744936 / 1000000 }
          )
        )
      )
      (.split (3 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 9, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
            upper := 148932564 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 140253998 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 144668713 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (0 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 144000629 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 152545915 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 148793221 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 165279817 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
                upper := 158124963 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 165519588 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 158710353 / 1000000 }
            )
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 136879671 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 128194036 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
              upper := 141653445 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
              upper := 142905927 / 1000000 }
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
      (179425964060461765201257 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard362
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
