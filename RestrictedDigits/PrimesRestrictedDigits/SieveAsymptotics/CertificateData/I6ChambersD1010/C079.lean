import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C079
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C079

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
    (.split 0 (5837 / 38335)
      (.split 3 (64996 / 115005)
        (.split 5 (50009 / 115005)
          (.zeroFace 1 0
            (.zeroFace 4 1
              (.retain 0)
            )
          )
          (.zeroFace 4 1
            (.split 5 (1 / 2)
              (.retain 300)
              (.zeroFace 9 0
                (.retain 341)
              )
            )
          )
        )
        (.zeroFace 1 0
          (.zeroFace 4 2
            (.retain 0)
          )
        )
      )
      (.split 2 (5837 / 38335)
        (.split 5 (50009 / 115005)
          (.zeroFace 1 0
            (.zeroFace 4 2
              (.retain 0)
            )
          )
          (.zeroFace 4 2
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.split 5 (1 / 2)
                  (.retain 631)
                  (.zeroFace 9 0
                    (.retain 828)
                  )
                )
                (.zeroFace 9 0
                  (.retain 828)
                )
              )
              (.zeroFace 9 3
                (.retain 828)
              )
            )
          )
        )
        (.zeroFace 4 2
          (.exclude 9)
        )
      )
    )
    (.zeroFace 0 1
      (.split 1 (64996 / 115005)
        (.split 3 (64996 / 115005)
          (.zeroFace 4 0
            (.zeroFace 9 0
              (.retain 0)
            )
          )
          (.split 4 (32498 / 38335)
            (.zeroFace 4 0
              (.retain 0)
            )
            (.zeroFace 1 0
              (.zeroFace 4 0
                (.retain 0)
              )
            )
          )
        )
        (.split 2 (32498 / 38335)
          (.split 4 (32498 / 38335)
            (.zeroFace 4 2
              (.retain 0)
            )
            (.zeroFace 1 0
              (.zeroFace 4 2
                (.retain 0)
              )
            )
          )
          (.zeroFace 1 2
            (.zeroFace 4 0
              (.retain 0)
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 3) (i6D1006LeafValid 2 0 3) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 3) root = 0 := by
  decide +kernel

end C079
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
