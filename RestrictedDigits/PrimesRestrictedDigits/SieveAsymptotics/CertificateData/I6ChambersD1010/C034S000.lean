import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C034S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C034S000

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)],
    ![(180001 / 1000000), (180001 / 1000000), (319999 / 2500000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (9546 / 17425));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (9546 / 17425));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1895 / 23637)
    (.split 3 (6212 / 7879)
      (.split 2 (259984 / 320001)
        (.split 4 (479936 / 780021)
          (.split 5 (479936 / 780021)
            (.split 0 (558995981 / 559238406)
              (.split 4 (25 / 120034)
                (.split 5 (25 / 120034)
                  (.zeroFace 10 0
                    (.retain 229)
                  )
                  (.retain (15235086528 / 66685001))
                )
                (.retain (22852629792 / 100048339))
              )
              (.split 1 (558995981 / 559238406)
                (.split 5 (25 / 120034)
                  (.zeroFace 10 0
                    (.retain 228)
                  )
                  (.retain (212940804401856 / 931846300327))
                )
                (.zeroFace 10 1
                  (.retain 229)
                )
              )
            )
            (.zeroFace 8 0
              (.split 0 (558995981 / 559238406)
                (.split 3 (242425 / 559238406)
                  (.split 5 (558995981 / 559238406)
                    (.retain 228)
                    (.zeroFace 10 0
                      (.retain 229)
                    )
                  )
                  (.retain 229)
                )
                (.split 2 (558995981 / 559238406)
                  (.split 5 (558995981 / 559238406)
                    (.retain 228)
                    (.zeroFace 10 0
                      (.retain 228)
                    )
                  )
                  (.zeroFace 10 1
                    (.retain 229)
                  )
                )
              )
            )
          )
          (.zeroFace 8 0
            (.split 2 (558995981 / 559238406)
              (.split 4 (558995981 / 559238406)
                (.split 5 (558995981 / 559238406)
                  (.retain 229)
                  (.zeroFace 10 0
                    (.retain 229)
                  )
                )
                (.zeroFace 10 0
                  (.retain 229)
                )
              )
              (.zeroFace 10 3
                (.retain 229)
              )
            )
          )
        )
        (.zeroFace 8 3
          (.exclude 10)
        )
      )
      (.split 4 (24848 / 55153)
        (.split 2 (259984 / 320001)
          (.split 4 (179920 / 600039)
            (.split 5 (479936 / 780021)
              (.split 0 (558995981 / 559238406)
                (.split 4 (25 / 120034)
                  (.split 5 (25 / 120034)
                    (.zeroFace 10 0
                      (.retain 231)
                    )
                    (.retain (14254812864 / 62124659))
                  )
                  (.retain (21458803176 / 93206401))
                )
                (.split 1 (558995981 / 559238406)
                  (.split 5 (25 / 120034)
                    (.zeroFace 10 0
                      (.retain 229)
                    )
                    (.retain (127925713152 / 558995981))
                  )
                  (.zeroFace 10 1
                    (.retain 231)
                  )
                )
              )
              (.zeroFace 8 0
                (.split 0 (558995981 / 559238406)
                  (.split 3 (242425 / 559238406)
                    (.split 5 (558995981 / 559238406)
                      (.retain 230)
                      (.zeroFace 10 0
                        (.retain 231)
                      )
                    )
                    (.retain 231)
                  )
                  (.split 2 (558995981 / 559238406)
                    (.split 5 (558995981 / 559238406)
                      (.retain 229)
                      (.zeroFace 10 0
                        (.retain 229)
                      )
                    )
                    (.zeroFace 10 1
                      (.retain 231)
                    )
                  )
                )
              )
            )
            (.zeroFace 8 0
              (.split 2 (558995981 / 559238406)
                (.split 4 (558995981 / 559238406)
                  (.split 5 (558995981 / 559238406)
                    (.retain 231)
                    (.zeroFace 10 0
                      (.retain 231)
                    )
                  )
                  (.zeroFace 10 0
                    (.retain 231)
                  )
                )
                (.zeroFace 10 3
                  (.retain 231)
                )
              )
            )
          )
          (.zeroFace 8 3
            (.exclude 10)
          )
        )
        (.zeroFace 6 0
          (.exclude 8)
        )
      )
    )
    (.split 2 (1919944 / 2340063)
      (.split 4 (259984 / 320001)
        (.split 5 (479936 / 780021)
          (.split 1 (59992 / 60017)
            (.split 3 (558995981 / 559238406)
              (.split 5 (25 / 120034)
                (.zeroFace 10 0
                  (.retain 228)
                )
                (.retain (72456768 / 9475))
              )
              (.zeroFace 10 0
                (.retain 228)
              )
            )
            (.zeroFace 10 2
              (.retain 228)
            )
          )
          (.zeroFace 8 0
            (.split 2 (59992 / 60017)
              (.split 4 (558995981 / 559238406)
                (.split 5 (59992 / 60017)
                  (.retain 228)
                  (.zeroFace 10 0
                    (.retain 228)
                  )
                )
                (.zeroFace 10 0
                  (.retain 228)
                )
              )
              (.zeroFace 10 3
                (.retain 228)
              )
            )
          )
        )
        (.zeroFace 8 0
          (.exclude 10)
        )
      )
      (.zeroFace 8 3
        (.exclude 10)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 0) (i6D1006LeafValid 1 1 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0) root = (5309 / 100000000000000) := by
  decide +kernel

end C034S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
