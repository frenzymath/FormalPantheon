import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C119
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C119

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, false]))

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
    (.split 0 (379 / 6970)
      (.zeroFace 1 0
        (.exclude 9)
      )
      (.split 1 (758 / 3485)
        (.zeroFace 1 0
          (.exclude 9)
        )
        (.split 2 (758 / 3485)
          (.zeroFace 1 0
            (.split 0 (2 / 3)
              (.split 4 (1 / 3)
                (.split 5 (1 / 2)
                  (.retain 0)
                  (.zeroFace 9 0
                    (.retain 0)
                  )
                )
                (.zeroFace 9 0
                  (.retain 0)
                )
              )
              (.split 1 (1 / 2)
                (.split 5 (1 / 2)
                  (.retain 0)
                  (.zeroFace 9 0
                    (.retain 0)
                  )
                )
                (.retain 0)
              )
            )
          )
          (.split 2 (1 / 4)
            (.split 4 (1 / 3)
              (.split 5 (1 / 2)
                (.split 1 (1 / 3)
                  (.retain (739004300000 / 72459558809))
                  (.split 2 (1 / 9)
                    (.retain (1728487440000 / 72459558809))
                    (.zeroFace 10 1
                      (.retain 24)
                    )
                  )
                )
                (.zeroFace 9 0
                  (.split 2 (1 / 3)
                    (.split 5 (1 / 3)
                      (.retain 20)
                      (.zeroFace 10 0
                        (.retain 30)
                      )
                    )
                    (.zeroFace 10 1
                      (.retain 10)
                    )
                  )
                )
              )
              (.zeroFace 9 0
                (.zeroFace 10 3
                  (.retain 0)
                )
              )
            )
            (.zeroFace 9 3
              (.exclude 10)
            )
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 2 (6591 / 6970)
        (.split 4 (6591 / 6970)
          (.split 5 (2727 / 3485)
            (.exclude 9)
            (.zeroFace 1 0
              (.exclude 9)
            )
          )
          (.zeroFace 1 0
            (.exclude 9)
          )
        )
        (.zeroFace 1 3
          (.exclude 9)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 6) (i6D1006LeafValid 2 4 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 6) root = (75361047 / 50000000000000) := by
  decide +kernel

end C119
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
