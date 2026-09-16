import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S019
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S019

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (244997 / 2000000)],
    ![(1 / 7), (1 / 7), (1 / 7)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 24395));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 24395));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (32498 / 115005)
    (.split 3 (82507 / 115005)
      (.zeroFace 13 0
        (.retain 0)
      )
      (.split 4 (577549 / 817542)
        (.zeroFace 13 0
          (.retain 10)
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 4 (1 / 2)
              (.split 2 (1 / 2)
                (.retain (5446622366640000000 / 212868597415202497))
                (.retain (3699097909015680000 / 212868597415202497))
              )
              (.retain (4236588488882880000 / 212868597415202497))
            )
            (.split 3 (1 / 2)
              (.retain (1951721037046080000 / 212868597415202497))
              (.retain (3190210798936320000 / 212868597415202497))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (3567528865288800000 / 212868597415202497))
              (.retain (1476555358318560000 / 212868597415202497))
            )
            (.retain (2155307197990320000 / 212868597415202497))
          )
        )
      )
    )
    (.zeroFace 13 1
      (.retain 0)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (1306593779 / 100000000000000) := by
  decide +kernel

end C100S019
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
