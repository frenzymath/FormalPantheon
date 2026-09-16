import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C040
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C040

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

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
    (.split 4 (2 / 3)
      (.split 5 (1 / 2)
        (.split 0 (379 / 3485)
          (.split 3 (12424 / 17425)
            (.zeroFace 3 0
              (.exclude 8)
            )
            (.split 4 (6212 / 24395)
              (.zeroFace 3 0
                (.exclude 8)
              )
              (.split 0 (16249 / 17083)
                (.split 3 (2085 / 17083)
                  (.zeroFace 8 0
                    (.retain 0)
                  )
                  (.split 4 (5838 / 17083)
                    (.zeroFace 8 0
                      (.retain 17)
                    )
                    (.retain (4709385625 / 290046852))
                  )
                )
                (.zeroFace 8 1
                  (.retain 0)
                )
              )
            )
          )
          (.zeroFace 3 1
            (.exclude 8)
          )
        )
        (.zeroFace 1 0
          (.split 0 (379 / 3485)
            (.split 3 (3106 / 3485)
              (.zeroFace 3 0
                (.exclude 8)
              )
              (.split 4 (12424 / 17425)
                (.zeroFace 3 0
                  (.exclude 8)
                )
                (.split 0 (16249 / 17083)
                  (.split 3 (834 / 17083)
                    (.zeroFace 8 0
                      (.retain 0)
                    )
                    (.split 4 (2085 / 17083)
                      (.zeroFace 8 0
                        (.retain 0)
                      )
                      (.retain 0)
                    )
                  )
                  (.zeroFace 8 1
                    (.retain 0)
                  )
                )
              )
            )
            (.zeroFace 3 1
              (.exclude 8)
            )
          )
        )
      )
      (.zeroFace 1 0
        (.split 2 (379 / 3485)
          (.split 4 (379 / 3485)
            (.split 5 (379 / 3485)
              (.split 2 (16249 / 17083)
                (.split 4 (16249 / 17083)
                  (.split 5 (16249 / 17083)
                    (.retain 0)
                    (.zeroFace 8 0
                      (.retain 0)
                    )
                  )
                  (.zeroFace 8 0
                    (.retain 0)
                  )
                )
                (.zeroFace 8 3
                  (.retain 0)
                )
              )
              (.zeroFace 3 0
                (.exclude 8)
              )
            )
            (.zeroFace 3 0
              (.exclude 8)
            )
          )
          (.zeroFace 3 3
            (.exclude 8)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 1 3
        (.exclude 3)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 0) (i6D1006LeafValid 1 4 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 0) root = (7535017 / 50000000000000) := by
  decide +kernel

end C040
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
