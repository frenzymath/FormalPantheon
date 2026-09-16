import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 373
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard373

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'right'), (2, 'left'), (4, 'right'), (3, 'left'), (5, 'left')), 20 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![229997 / 2000000, 35001 / 1600000, 35001 / 1600000],
    ![52499 / 500000, 365013 / 8000000, 215007 / 8000000],
    ![439993 / 4000000, 615021 / 16000000, 93003 / 3200000],
    ![229997 / 2000000, 325011 / 8000000, 35001 / 1600000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 125676670 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 125552622 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 130756598 / 1000000 }
          )
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 15, 9, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
            upper := 139950725 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![15, 15, 15, 15, 9, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
            upper := 142520083 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 135746707 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 9, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 136274588 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 9, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 152585364 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 152790617 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 153635989 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 150304534 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 143798980 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 144043168 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 151796397 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 145246372 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 144616676 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 158004232 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 162024038 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 150540192 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 155485266 / 1000000 }
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
      (34559070201137025676233 / 1638400000000000000000000000 : Rat) := by
  decide +kernel

end Shard373
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
