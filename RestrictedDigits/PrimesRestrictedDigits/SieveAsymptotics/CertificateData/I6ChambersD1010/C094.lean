import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C094
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C094

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

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
    (.split 2 (5837 / 38335)
      (.split 4 (82507 / 115005)
        (.split 5 (50009 / 115005)
          (.zeroFace 1 0
            (.zeroFace 4 1
              (.zeroFace 5 0
                (.retain 0)
              )
            )
          )
          (.zeroFace 4 1
            (.zeroFace 5 0
              (.retain 0)
            )
          )
        )
        (.zeroFace 4 1
          (.zeroFace 5 0
            (.split 2 (2 / 3)
              (.split 4 (2 / 3)
                (.split 5 (2 / 3)
                  (.split 2 (75004 / 82507)
                    (.split 4 (75004 / 82507)
                      (.split 5 (75004 / 82507)
                        (.retain 105)
                        (.zeroFace 15 0
                          (.retain 138)
                        )
                      )
                      (.zeroFace 15 0
                        (.retain 138)
                      )
                    )
                    (.zeroFace 15 3
                      (.retain 138)
                    )
                  )
                  (.zeroFace 9 0
                    (.exclude 15)
                  )
                )
                (.zeroFace 9 0
                  (.exclude 15)
                )
              )
              (.zeroFace 9 3
                (.exclude 15)
              )
            )
          )
        )
      )
      (.zeroFace 4 1
        (.zeroFace 5 0
          (.exclude 9)
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 4 0
        (.zeroFace 5 0
          (.exclude 9)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 4) (i6D1006LeafValid 2 0 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 4) root = 0 := by
  decide +kernel

end C094
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
