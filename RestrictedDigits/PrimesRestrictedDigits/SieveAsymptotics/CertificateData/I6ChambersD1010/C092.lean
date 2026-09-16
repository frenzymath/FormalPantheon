import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C092
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C092

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
    (.zeroFace 4 1
      (.zeroFace 5 0
        (.split 2 (9546 / 17425)
          (.split 4 (9546 / 17425)
            (.split 5 (9546 / 17425)
              (.zeroFace 10 0
                (.exclude 13)
              )
              (.split 1 (59992 / 472527)
                (.split 3 (59992 / 472527)
                  (.split 5 (412535 / 472527)
                    (.zeroFace 13 0
                      (.exclude 15)
                    )
                    (.split 1 (18751 / 82507)
                      (.split 3 (18751 / 82507)
                        (.split 5 (63756 / 82507)
                          (.zeroFace 15 0
                            (.retain 1177)
                          )
                          (.retain 1390)
                        )
                        (.zeroFace 15 0
                          (.retain 1177)
                        )
                      )
                      (.zeroFace 15 2
                        (.retain 1177)
                      )
                    )
                  )
                  (.zeroFace 13 0
                    (.exclude 15)
                  )
                )
                (.zeroFace 13 2
                  (.exclude 15)
                )
              )
            )
            (.split 0 (59992 / 472527)
              (.split 4 (412535 / 472527)
                (.split 5 (412535 / 472527)
                  (.zeroFace 13 0
                    (.exclude 15)
                  )
                  (.split 1 (18751 / 82507)
                    (.split 3 (18751 / 82507)
                      (.split 5 (63756 / 82507)
                        (.zeroFace 15 0
                          (.retain 1177)
                        )
                        (.retain 1390)
                      )
                      (.zeroFace 15 0
                        (.retain 1177)
                      )
                    )
                    (.zeroFace 15 2
                      (.retain 1177)
                    )
                  )
                )
                (.split 0 (18751 / 82507)
                  (.split 4 (63756 / 82507)
                    (.split 5 (63756 / 82507)
                      (.zeroFace 15 0
                        (.retain 1177)
                      )
                      (.retain 1390)
                    )
                    (.retain 1265)
                  )
                  (.split 1 (18751 / 82507)
                    (.split 5 (63756 / 82507)
                      (.zeroFace 15 0
                        (.retain 1177)
                      )
                      (.retain 1390)
                    )
                    (.zeroFace 15 1
                      (.retain 1177)
                    )
                  )
                )
              )
              (.split 1 (59992 / 472527)
                (.split 5 (412535 / 472527)
                  (.zeroFace 13 0
                    (.exclude 15)
                  )
                  (.split 1 (18751 / 82507)
                    (.split 3 (18751 / 82507)
                      (.split 5 (63756 / 82507)
                        (.zeroFace 15 0
                          (.retain 1177)
                        )
                        (.retain 1390)
                      )
                      (.zeroFace 15 0
                        (.retain 1177)
                      )
                    )
                    (.zeroFace 15 2
                      (.retain 1177)
                    )
                  )
                )
                (.zeroFace 13 1
                  (.exclude 15)
                )
              )
            )
          )
          (.split 2 (412535 / 472527)
            (.split 4 (412535 / 472527)
              (.split 5 (412535 / 472527)
                (.zeroFace 13 0
                  (.exclude 15)
                )
                (.split 1 (18751 / 82507)
                  (.split 3 (18751 / 82507)
                    (.split 5 (63756 / 82507)
                      (.zeroFace 15 0
                        (.retain 1177)
                      )
                      (.retain 1390)
                    )
                    (.zeroFace 15 0
                      (.retain 1177)
                    )
                  )
                  (.zeroFace 15 2
                    (.retain 1177)
                  )
                )
              )
              (.split 0 (18751 / 82507)
                (.split 4 (63756 / 82507)
                  (.split 5 (63756 / 82507)
                    (.zeroFace 15 0
                      (.retain 1177)
                    )
                    (.retain 1390)
                  )
                  (.retain 1265)
                )
                (.split 1 (18751 / 82507)
                  (.split 5 (63756 / 82507)
                    (.zeroFace 15 0
                      (.retain 1177)
                    )
                    (.retain 1390)
                  )
                  (.zeroFace 15 1
                    (.retain 1177)
                  )
                )
              )
            )
            (.split 2 (63756 / 82507)
              (.split 4 (63756 / 82507)
                (.split 5 (63756 / 82507)
                  (.zeroFace 15 0
                    (.retain 1177)
                  )
                  (.retain 1390)
                )
                (.retain 1265)
              )
              (.retain 802)
            )
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 4 0
        (.zeroFace 5 0
          (.retain 0)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = 0 := by
  decide +kernel

end C092
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
