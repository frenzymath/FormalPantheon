import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C019S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C019S000

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(54167 / 375000), (54167 / 375000), (54167 / 375000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 10455));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 10455));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (758 / 10455)
    (.split 5 (758 / 10455)
      (.zeroFace 1 0
        (.split 1 (1516 / 9697)
          (.split 3 (6970 / 9697)
            (.split 5 (8181 / 9697)
              (.split 4 (8181 / 8939)
                (.split 2 (3 / 4)
                  (.split 4 (10455 / 19394)
                    (.split 5 (3 / 4)
                      (.retain 0)
                      (.zeroFace 9 0
                        (.retain 0)
                      )
                    )
                    (.zeroFace 9 0
                      (.retain 0)
                    )
                  )
                  (.zeroFace 9 3
                    (.retain 0)
                  )
                )
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
              (.zeroFace 5 0
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
            )
            (.split 4 (9318 / 9697)
              (.split 5 (8181 / 8939)
                (.split 2 (3 / 4)
                  (.split 5 (10455 / 19394)
                    (.retain 0)
                    (.zeroFace 9 0
                      (.retain 0)
                    )
                  )
                  (.zeroFace 9 1
                    (.retain 0)
                  )
                )
                (.zeroFace 6 0
                  (.zeroFace 9 1
                    (.retain 0)
                  )
                )
              )
              (.zeroFace 6 0
                (.zeroFace 9 3
                  (.retain 0)
                )
              )
            )
          )
          (.split 0 (379 / 9697)
            (.split 4 (9318 / 9697)
              (.split 5 (3 / 4)
                (.retain 0)
                (.zeroFace 9 0
                  (.retain 0)
                )
              )
              (.zeroFace 6 0
                (.zeroFace 9 0
                  (.retain 0)
                )
              )
            )
            (.split 1 (1 / 4)
              (.split 5 (3 / 4)
                (.retain 0)
                (.zeroFace 9 0
                  (.retain 0)
                )
              )
              (.retain 0)
            )
          )
        )
      )
      (.split 1 (3032 / 22805)
        (.split 3 (13940 / 20531)
          (.zeroFace 5 0
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.split 4 (6970 / 9697)
            (.zeroFace 5 0
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
        )
        (.split 2 (1516 / 9697)
          (.split 4 (6970 / 9697)
            (.zeroFace 5 0
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.split 0 (379 / 9697)
            (.zeroFace 6 0
              (.zeroFace 9 0
                (.retain 0)
              )
            )
            (.split 1 (22805 / 95768)
              (.zeroFace 9 0
                (.retain 2)
              )
              (.split 2 (1 / 4)
                (.zeroFace 9 0
                  (.retain 1)
                )
                (.retain (12747678480000 / 27462172788611))
              )
            )
          )
        )
      )
    )
    (.split 1 (3032 / 22805)
      (.split 3 (4773 / 6970)
        (.split 5 (6591 / 20531)
          (.zeroFace 6 0
            (.exclude 9)
          )
          (.zeroFace 5 0
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
        )
        (.zeroFace 6 0
          (.exclude 9)
        )
      )
      (.split 0 (3032 / 85535)
        (.zeroFace 6 0
          (.exclude 9)
        )
        (.split 2 (379 / 9697)
          (.zeroFace 6 0
            (.zeroFace 9 0
              (.retain 0)
            )
          )
          (.split 0 (85535 / 95768)
            (.zeroFace 9 0
              (.retain 2)
            )
            (.split 1 (22805 / 95768)
              (.zeroFace 9 0
                (.retain 2)
              )
              (.retain (1615618777434000 / 1740103130332897))
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 6) (i6D1006LeafValid 1 1 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 6) root = (32501 / 50000000000000) := by
  decide +kernel

end C019S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
