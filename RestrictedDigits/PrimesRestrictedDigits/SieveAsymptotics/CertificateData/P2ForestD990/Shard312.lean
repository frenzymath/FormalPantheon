import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 312
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard312

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left'), (3, 'right'), (4, 'left'), (2, 'left'), (5, 'right')), 10 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![100831 / 1000000, 81669 / 8000000, 35001 / 8000000],
    ![181661 / 2000000, 8667 / 200000, 0],
    ![84997 / 1000000, 185007 / 4000000, 35001 / 4000000],
    ![100831 / 1000000, 9267 / 320000, 35001 / 8000000]
  ]

theorem root_eq_path :
    root = (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            (.split (4 : Fin 6)
              (.split (5 : Fin 6)
                (.retain
                  { baseline := 9
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 57711464 / 1000000 }
                )
                (.retain
                  { baseline := 8
                    legacy := 14
                    middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                    inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                    upper := 59707620 / 1000000 }
                )
              )
              (.retain
                { baseline := 8
                  legacy := 2
                  middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                  inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                  upper := 54326990 / 1000000 }
              )
            )
            (.retain
              { baseline := 8
                legacy := 2
                middle := ![2, 2, 2, 2, 2, 2, 2, 2]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
                upper := 50507760 / 1000000 }
            )
          )
          (.retain
            { baseline := 8
              legacy := 2
              middle := ![2, 2, 2, 2, 2, 2, 2, 2]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 62759213 / 1000000 }
          )
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 60211175 / 1000000 }
        )
      )
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 47859561 / 1000000 }
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 79318132 / 1000000 }
        )
        (.retain
          { baseline := 8
            legacy := 2
            middle := ![2, 2, 2, 2, 2, 2, 2, 2]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 91950497 / 1000000 }
        )
      )
      (.retain
        { baseline := 8
          legacy := 2
          middle := ![2, 2, 2, 2, 2, 2, 2, 2]
          inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
          upper := 65186654 / 1000000 }
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (23316966553221128161143 / 1024000000000000000000000000 : Rat) := by
  decide +kernel

end Shard312
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
