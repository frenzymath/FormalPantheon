import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 403
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard403

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'left'), (2, 'right'), (1, 'left'), (3, 'left'), (5, 'right'), (1, 'left')), 17 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![359989 / 4000000, 53127 / 1000000, 53127 / 1000000],
    ![37999 / 400000, 240009 / 4000000, 82503 / 2000000],
    ![84997 / 1000000, 26001 / 400000, 26001 / 400000],
    ![37999 / 400000, 81003 / 1600000, 81003 / 1600000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
            upper := 324944122 / 1000000 }
        )
        (.split (3 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 31, 31, 31, 31]
              upper := 355936764 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 14, 14, 31, 31, 31]
              upper := 339191725 / 1000000 }
          )
        )
      )
      (.split (2 : Fin 6)
        (.retain
          { baseline := 1
            legacy := 9
            middle := ![15, 15, 15, 15, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
            upper := 319253279 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 327024132 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 333205969 / 1000000 }
          )
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 305243064 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
              upper := 316592935 / 1000000 }
          )
        )
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 31, 31, 31]
                upper := 299111962 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 308033646 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 300783373 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 293474034 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 14, 14, 31, 31]
                upper := 301724968 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 294501895 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 272980596 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 9
                middle := ![15, 15, 15, 15, 15, 15, 15, 15]
                inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
                upper := 280478234 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 9
              middle := ![15, 15, 15, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 14, 31, 31]
              upper := 295778984 / 1000000 }
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
      (188820370627166354896089 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard403
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
