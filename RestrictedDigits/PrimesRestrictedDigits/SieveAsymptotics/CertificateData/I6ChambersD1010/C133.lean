import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C133
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C133

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, true]))

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
    (.split 2 (36667 / 76670)
      (.split 4 (75002 / 115005)
        (.split 5 (75002 / 115005)
          (.split 0 (36667 / 40003)
            (.split 3 (5004 / 40003)
              (.exclude 10)
              (.split 4 (5004 / 40003)
                (.exclude 10)
                (.zeroFace 6 0
                  (.exclude 10)
                )
              )
            )
            (.exclude 10)
          )
          (.zeroFace 1 0
            (.split 0 (36667 / 40003)
              (.split 3 (3336 / 40003)
                (.exclude 10)
                (.split 4 (5004 / 40003)
                  (.exclude 10)
                  (.zeroFace 6 0
                    (.exclude 10)
                  )
                )
              )
              (.exclude 10)
            )
          )
        )
        (.zeroFace 1 0
          (.split 2 (36667 / 40003)
            (.split 4 (36667 / 40003)
              (.split 5 (36667 / 40003)
                (.zeroFace 6 0
                  (.exclude 10)
                )
                (.exclude 10)
              )
              (.exclude 10)
            )
            (.exclude 10)
          )
        )
      )
      (.zeroFace 1 3
        (.exclude 10)
      )
    )
    (.zeroFace 0 1
      (.exclude 1)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 0) (i6D1006LeafValid 2 6 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0) root = 0 := by
  decide +kernel

end C133
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
