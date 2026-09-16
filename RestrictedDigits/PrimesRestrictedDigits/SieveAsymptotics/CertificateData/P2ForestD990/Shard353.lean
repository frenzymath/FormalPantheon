import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 353
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard353

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left'), (5, 'left')), 30 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![52499 / 500000, 365013 / 8000000, 365013 / 8000000],
    ![52499 / 500000, 27501 / 500000, 365013 / 8000000],
    ![229997 / 2000000, 325011 / 8000000, 325011 / 8000000],
    ![124999 / 1000000, 105003 / 4000000, 105003 / 4000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 9, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 131680742 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 143713855 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 149418852 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 164375734 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 159639207 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 9, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 157890313 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 172106442 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 174667486 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 164797645 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 173444913 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 182340857 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 191468521 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 191059958 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 177267093 / 1000000 }
            )
          )
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                  upper := 176097252 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 9, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                  upper := 182057464 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 9, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 179960203 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                  upper := 178706158 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                  upper := 183949364 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 187563448 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 181879247 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 188626643 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 197837610 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 9, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 185492262 / 1000000 }
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 200522607 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 195599143 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 202698272 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 9, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 206489236 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
                upper := 207135125 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
                upper := 212019233 / 1000000 }
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
      (214930643667636965846409 / 8192000000000000000000000000 : Rat) := by
  decide +kernel

end Shard353
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
