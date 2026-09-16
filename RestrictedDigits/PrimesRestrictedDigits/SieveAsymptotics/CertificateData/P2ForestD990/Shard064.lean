import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 64
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard064

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'right'), (3, 'left'), (1, 'right'), (2, 'left')), 31 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![132499 / 1000000, 35001 / 8000000, 35001 / 8000000],
    ![68333 / 500000, 81669 / 4000000, 35001 / 4000000],
    ![116333 / 800000, 11667 / 1000000, 0],
    ![284999 / 2000000, 35001 / 4000000, 35001 / 4000000]
  ]

theorem root_eq_path :
    root = ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 14, 14, 25]
            upper := 29811502 / 1000000 }
        )
        (.retain
          { baseline := 1
            legacy := 1
            middle := ![1, 1, 1, 1, 1, 1, 1, 1]
            inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
            upper := 20837748 / 1000000 }
        )
      )
      (.split (1 : Fin 6)
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![1, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
              upper := 22615433 / 1000000 }
          )
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                upper := 19408347 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                upper := 15672633 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                  upper := 25729758 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                  upper := 29736107 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 31857358 / 1000000 }
            )
          )
          (.split (2 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                  upper := 30775302 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 26077618 / 1000000 }
              )
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 27054607 / 1000000 }
            )
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 23028932 / 1000000 }
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                  upper := 29975601 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 22425684 / 1000000 }
              )
            )
          )
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 25]
                upper := 20064621 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                upper := 13002286 / 1000000 }
            )
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 26679836 / 1000000 }
            )
            (.split (3 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                  upper := 26009601 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                  upper := 32940535 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 26480224 / 1000000 }
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 18417010 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![1, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 14, 8]
                  upper := 7822689 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 12]
                  upper := 13456226 / 1000000 }
              )
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![9, 1, 1, 1, 1, 1, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 21752447 / 1000000 }
          )
        )
        (.split (2 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![9, 1, 1, 1, 1, 1, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 25746823 / 1000000 }
            )
            (.split (1 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![8, 1, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 22908739 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 26754285 / 1000000 }
              )
            )
          )
          (.split (1 : Fin 6)
            (.split (5 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 23857504 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![8, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 21842763 / 1000000 }
              )
            )
            (.split (0 : Fin 6)
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                  upper := 26027560 / 1000000 }
              )
              (.retain
                { baseline := 1
                  legacy := 1
                  middle := ![14, 9, 1, 1, 1, 1, 1, 1]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 27518012 / 1000000 }
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
      (2386207569733044431517 / 409600000000000000000000000 : Rat) := by
  decide +kernel

end Shard064
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
