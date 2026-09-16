import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C002

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (2 / 3)
    (.split 2 (75002 / 115005)
      (.split 4 (190007 / 230010)
        (.split 5 (190007 / 230010)
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.split 2 (1 / 2)
                (.retain (5802939288000000 / 64014401080027))
                (.retain (3052793793600000 / 64014401080027))
              )
              (.retain (1557985613760000 / 64014401080027))
            )
            (.split 4 (1 / 2)
              (.split 2 (1 / 2)
                (.retain (5821293934080000 / 64014401080027))
                (.retain (3073361561280000 / 64014401080027))
              )
              (.retain (1567168302240000 / 64014401080027))
            )
          )
          (.zeroFace 1 0
            (.retain 0)
          )
        )
        (.zeroFace 1 0
          (.retain 0)
        )
      )
      (.zeroFace 1 3
        (.retain 0)
      )
    )
    (.zeroFace 0 1
      (.exclude 1)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 0) (i6D1006LeafValid 0 1 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0) root = (4166787571 / 50000000000000) := by
  decide +kernel

end C002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
