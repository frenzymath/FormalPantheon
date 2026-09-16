import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C009S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C009S000

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (29167 / 30668)
    (.split 3 (1501 / 23001)
      (.split 1 (287501 / 322500)
        (.split 3 (287501 / 322500)
          (.zeroFace 3 0
            (.exclude 8)
          )
          (.split 4 (287501 / 552510)
            (.zeroFace 3 0
              (.split 0 (1289153166 / 2204270167)
                (.split 3 (915117001 / 2204270167)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                  (.split 4 (915117001 / 2204270167)
                    (.zeroFace 8 0
                      (.exclude 9)
                    )
                    (.exclude 9)
                  )
                )
                (.zeroFace 8 1
                  (.exclude 9)
                )
              )
            )
            (.split 0 (69998 / 287501)
              (.split 3 (217503 / 287501)
                (.split 5 (1289153166 / 2204270167)
                  (.exclude 9)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                )
                (.exclude 9)
              )
              (.split 2 (1289153166 / 2204270167)
                (.split 5 (1289153166 / 2204270167)
                  (.exclude 9)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                )
                (.zeroFace 8 1
                  (.exclude 9)
                )
              )
            )
          )
        )
        (.split 2 (287501 / 552510)
          (.split 4 (287501 / 552510)
            (.zeroFace 3 0
              (.split 1 (915117001 / 2204270167)
                (.split 3 (915117001 / 2204270167)
                  (.split 5 (1289153166 / 2204270167)
                    (.exclude 9)
                    (.zeroFace 8 0
                      (.exclude 9)
                    )
                  )
                  (.exclude 9)
                )
                (.exclude 9)
              )
            )
            (.split 1 (915117001 / 2204270167)
              (.split 3 (217503 / 287501)
                (.split 5 (1289153166 / 2204270167)
                  (.exclude 9)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
          )
          (.split 1 (217503 / 287501)
            (.split 3 (217503 / 287501)
              (.split 5 (1289153166 / 2204270167)
                (.exclude 9)
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
        )
      )
      (.split 4 (3002 / 69003)
        (.split 2 (287501 / 552510)
          (.split 4 (854998 / 1650025)
            (.split 5 (287501 / 552510)
              (.zeroFace 3 0
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.exclude 9)
        )
        (.zeroFace 1 0
          (.exclude 9)
        )
      )
    )
    (.split 0 (150004 / 437505)
      (.split 3 (287501 / 322500)
        (.zeroFace 3 0
          (.exclude 8)
        )
        (.split 4 (287501 / 552510)
          (.zeroFace 3 0
            (.split 0 (1289153166 / 2204270167)
              (.split 3 (915117001 / 2204270167)
                (.zeroFace 8 0
                  (.exclude 9)
                )
                (.split 4 (915117001 / 2204270167)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                  (.exclude 9)
                )
              )
              (.zeroFace 8 1
                (.exclude 9)
              )
            )
          )
          (.split 0 (69998 / 287501)
            (.split 3 (217503 / 287501)
              (.split 5 (1289153166 / 2204270167)
                (.exclude 9)
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.exclude 9)
            )
            (.split 2 (1289153166 / 2204270167)
              (.split 5 (1289153166 / 2204270167)
                (.exclude 9)
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.zeroFace 8 1
                (.exclude 9)
              )
            )
          )
        )
      )
      (.zeroFace 3 1
        (.exclude 8)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 0 4 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = 0 := by
  decide +kernel

end C009S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
