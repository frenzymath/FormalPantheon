import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 477
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard477

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'right'), (4, 'right'), (3, 'left'), (1, 'left'), (5, 'left'), (5, 'right')), 15 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![84997 / 1000000, 185007 / 4000000, 295011 / 8000000],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1600000],
    ![149993 / 2000000, 280011 / 4000000, 335013 / 8000000],
    ![319987 / 4000000, 540021 / 8000000, 555021 / 16000000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 425605280 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 468920897 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 467779996 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 475569728 / 1000000 }
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 444790631 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 489213034 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 555841193 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 2, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 517186850 / 1000000 }
          )
        )
      )
    )
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.retain
          { baseline := 9
            legacy := 15
            middle := ![2, 2, 14, 14, 15, 15, 15, 15]
            inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
            upper := 405302320 / 1000000 }
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 420281012 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 391693445 / 1000000 }
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 438413713 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 14, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 447414821 / 1000000 }
          )
        )
        (.split (1 : Fin 6)
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 423388237 / 1000000 }
          )
          (.retain
            { baseline := 9
              legacy := 15
              middle := ![2, 2, 14, 15, 15, 15, 15, 15]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 2]
              upper := 402004618 / 1000000 }
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
      (53847310254402672214857 / 819200000000000000000000000 : Rat) := by
  decide +kernel

end Shard477
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
