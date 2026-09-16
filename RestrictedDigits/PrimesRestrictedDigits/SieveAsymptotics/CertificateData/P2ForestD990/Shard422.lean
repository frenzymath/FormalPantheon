import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 422
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard422

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'left'), (3, 'left'), (2, 'right'), (1, 'right'), (4, 'right')), 12 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![37999 / 400000, 82503 / 2000000, 82503 / 2000000],
    ![84997 / 1000000, 26001 / 400000, 185007 / 4000000],
    ![319987 / 4000000, 232509 / 4000000, 232509 / 4000000],
    ![699977 / 8000000, 236259 / 4000000, 79503 / 1600000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 369822369 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 14, 14, 31]
            upper := 396793400 / 1000000 }
        )
      )
      (.split (0 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 357088807 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 360851565 / 1000000 }
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (3 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 341031189 / 1000000 }
        )
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 337266617 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
            upper := 335974751 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 324090234 / 1000000 }
            )
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 324378674 / 1000000 }
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 9
                legacy := 15
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 315631691 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 9
                  legacy := 15
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 313882686 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 9
                  middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 304551711 / 1000000 }
              )
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
      (845257318113140924385537 / 16384000000000000000000000000 : Rat) := by
  decide +kernel

end Shard422
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
