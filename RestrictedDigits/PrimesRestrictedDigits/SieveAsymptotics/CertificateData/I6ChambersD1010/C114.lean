import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C114
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C114

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
    (.split 5 (1 / 2)
      (.zeroFace 6 0
        (.split 2 (758 / 24395)
          (.split 4 (758 / 24395)
            (.split 5 (1667 / 17425)
              (.zeroFace 10 0
                (.split 1 (1895 / 23637)
                  (.split 3 (1895 / 23637)
                    (.split 5 (21742 / 23637)
                      (.retain 39)
                      (.zeroFace 15 0
                        (.retain 41)
                      )
                    )
                    (.retain 38)
                  )
                  (.retain 37)
                )
              )
              (.split 1 (758 / 7121)
                (.split 3 (758 / 7121)
                  (.zeroFace 15 0
                    (.retain 31)
                  )
                  (.split 4 (1895 / 23637)
                    (.zeroFace 15 0
                      (.retain 34)
                    )
                    (.retain 35)
                  )
                )
                (.split 2 (1895 / 23637)
                  (.split 4 (1895 / 23637)
                    (.zeroFace 15 0
                      (.retain 38)
                    )
                    (.retain 37)
                  )
                  (.retain 36)
                )
              )
            )
            (.split 1 (758 / 7121)
              (.split 3 (758 / 3485)
                (.split 5 (6363 / 7121)
                  (.retain 25)
                  (.zeroFace 15 0
                    (.retain 24)
                  )
                )
                (.retain 17)
              )
              (.retain 26)
            )
          )
          (.split 1 (758 / 3485)
            (.split 3 (758 / 3485)
              (.split 5 (6363 / 7121)
                (.retain 17)
                (.zeroFace 15 0
                  (.retain 8)
                )
              )
              (.retain 9)
            )
            (.retain 9)
          )
        )
      )
      (.zeroFace 1 0
        (.zeroFace 6 0
          (.split 2 (758 / 3485)
            (.split 4 (758 / 3485)
              (.split 5 (758 / 3485)
                (.zeroFace 15 0
                  (.retain 0)
                )
                (.retain 0)
              )
              (.retain 0)
            )
            (.retain 0)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 1 0
        (.zeroFace 6 3
          (.retain 0)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = 0 := by
  decide +kernel

end C114
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
