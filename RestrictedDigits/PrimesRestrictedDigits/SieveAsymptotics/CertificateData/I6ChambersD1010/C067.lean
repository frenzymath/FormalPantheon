import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C067
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C067

abbrev label : i6D691Label :=
  (true, (2, ![false, false, false, true, false]))

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
    (.split 0 (5837 / 38335)
      (.zeroFace 1 0
        (.retain 0)
      )
      (.split 1 (5837 / 38335)
        (.zeroFace 1 0
          (.retain 0)
        )
        (.split 2 (5837 / 38335)
          (.zeroFace 1 0
            (.retain 0)
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (73119501640000 / 596609733759))
              (.retain (25024122560000 / 198869911253))
            )
            (.split 0 (1 / 2)
              (.retain (3030051160000 / 45893056443))
              (.retain (112734871000000 / 596609733759))
            )
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 2 (32498 / 38335)
        (.split 4 (32498 / 38335)
          (.split 5 (32498 / 38335)
            (.retain 131)
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
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 2) (i6D1006LeafValid 2 0 2) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 2) root = (1501587027 / 20000000000000) := by
  decide +kernel

end C067
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
