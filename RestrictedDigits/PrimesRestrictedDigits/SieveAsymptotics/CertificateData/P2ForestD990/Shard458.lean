import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 458
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard458

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left'), (1, 'right'), (4, 'left'), (5, 'right'), (1, 'left')), 29 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 255009 / 8000000, 255009 / 8000000],
    ![84997 / 1000000, 26001 / 400000, 295011 / 8000000],
    ![84997 / 1000000, 185007 / 4000000, 185007 / 4000000],
    ![37999 / 400000, 81003 / 1600000, 255009 / 8000000]
  ]

theorem root_eq_path :
    root = ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.split (2 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 15
                    middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 274853542 / 1000000 }
                )
                (.retain
                  { baseline := 9
                    legacy := 15
                    middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 294353341 / 1000000 }
                )
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 297096923 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 308740045 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 324047684 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 331732110 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![14, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 348558221 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 361994274 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 349444116 / 1000000 }
            )
          )
        )
      )
      (.split (5 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 274218313 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 289701637 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 304071016 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 301686732 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 311452937 / 1000000 }
            )
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 337009832 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 327175971 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![14, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 321489068 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 331582001 / 1000000 }
            )
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.split (4 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 261767176 / 1000000 }
              )
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 267065166 / 1000000 }
              )
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 273735837 / 1000000 }
            )
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 287539050 / 1000000 }
          )
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 303699087 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 299547122 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 306773032 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 302607905 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 14, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 292198139 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 304687710 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![2, 14, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 292260898 / 1000000 }
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
      (297044062509272156206011 / 3276800000000000000000000000 : Rat) := by
  decide +kernel

end Shard458
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
