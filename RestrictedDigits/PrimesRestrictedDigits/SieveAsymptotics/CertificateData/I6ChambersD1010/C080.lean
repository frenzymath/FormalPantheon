import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C080
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C080

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

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
              (.zeroFace 12 2
                (.retain 0)
              )
            )
          )
          (.zeroFace 4 1
            (.split 1 (82507 / 132516)
              (.split 3 (82507 / 132516)
                (.split 5 (1 / 2)
                  (.zeroFace 12 2
                    (.retain 631)
                  )
                  (.zeroFace 9 0
                    (.zeroFace 12 3
                      (.retain 828)
                    )
                  )
                )
                (.zeroFace 12 3
                  (.retain 0)
                )
              )
              (.zeroFace 12 3
                (.retain 0)
              )
            )
          )
        )
        (.zeroFace 4 1
          (.split 2 (2 / 3)
            (.split 4 (2 / 3)
              (.split 5 (50009 / 132516)
                (.exclude 12)
                (.zeroFace 9 0
                  (.exclude 12)
                )
              )
              (.zeroFace 9 0
                (.exclude 12)
              )
            )
            (.zeroFace 9 3
              (.exclude 12)
            )
          )
        )
      )
      (.zeroFace 4 1
        (.exclude 9)
      )
    )
    (.zeroFace 0 1
      (.zeroFace 4 0
        (.exclude 9)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 4) (i6D1006LeafValid 2 0 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 4) root = 0 := by
  decide +kernel

end C080
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
