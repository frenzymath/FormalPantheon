import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 340
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard340

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'left'), (4, 'left')), 16 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![229997 / 2000000, 325011 / 8000000, 325011 / 8000000],
    ![229997 / 2000000, 200007 / 4000000, 575019 / 16000000],
    ![52499 / 500000, 27501 / 500000, 27501 / 500000],
    ![124999 / 1000000, 90003 / 2000000, 105003 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 126658005 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 140846474 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 9, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
            upper := 145060205 / 1000000 }
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 9, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
            upper := 152062422 / 1000000 }
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 160612872 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 163059428 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
              upper := 193330932 / 1000000 }
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 205002191 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 13, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 216785851 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 187635902 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 31, 31, 31, 31, 31]
                upper := 192368393 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 182336083 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
                upper := 182116543 / 1000000 }
            )
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 9, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 168726826 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
              upper := 175160136 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 9, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 14, 14, 31, 31, 31, 31]
            upper := 172824283 / 1000000 }
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (198881675458109892755847 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard340
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
