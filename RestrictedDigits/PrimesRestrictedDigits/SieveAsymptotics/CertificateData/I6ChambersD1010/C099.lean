import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C099
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C099

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
    (.split 2 (758 / 3485)
      (.split 4 (2576 / 3485)
        (.split 5 (2576 / 3485)
          (.zeroFace 1 0
            (.zeroFace 5 0
              (.exclude 13)
            )
          )
          (.zeroFace 5 0
            (.exclude 13)
          )
        )
        (.zeroFace 5 0
          (.split 0 (379 / 1667)
            (.split 3 (1288 / 1667)
              (.exclude 13)
              (.split 4 (1 / 2)
                (.split 0 (26696287 / 57954204)
                  (.split 3 (31257917 / 57954204)
                    (.zeroFace 13 0
                      (.retain 507)
                    )
                    (.split 4 (18751 / 21252)
                      (.zeroFace 13 0
                        (.retain 454)
                      )
                      (.retain 595)
                    )
                  )
                  (.zeroFace 13 1
                    (.retain 507)
                  )
                )
                (.zeroFace 9 0
                  (.split 2 (26696287 / 57954204)
                    (.split 4 (26696287 / 57954204)
                      (.split 5 (26696287 / 57954204)
                        (.retain 654)
                        (.zeroFace 13 0
                          (.retain 507)
                        )
                      )
                      (.zeroFace 13 0
                        (.retain 507)
                      )
                    )
                    (.zeroFace 13 3
                      (.retain 507)
                    )
                  )
                )
              )
            )
            (.exclude 13)
          )
        )
      )
      (.zeroFace 5 0
        (.split 2 (1 / 4)
          (.split 4 (1288 / 1667)
            (.split 5 (1 / 4)
              (.split 0 (1667 / 10455)
                (.split 3 (8788 / 10455)
                  (.split 5 (1 / 9)
                    (.exclude 13)
                    (.zeroFace 10 0
                      (.exclude 13)
                    )
                  )
                  (.exclude 13)
                )
                (.split 2 (1 / 9)
                  (.split 5 (1 / 9)
                    (.exclude 13)
                    (.zeroFace 10 0
                      (.exclude 13)
                    )
                  )
                  (.zeroFace 10 1
                    (.exclude 13)
                  )
                )
              )
              (.zeroFace 9 0
                (.split 0 (1667 / 10455)
                  (.split 3 (8788 / 10455)
                    (.zeroFace 10 0
                      (.exclude 13)
                    )
                    (.split 4 (8788 / 10455)
                      (.zeroFace 10 0
                        (.exclude 13)
                      )
                      (.exclude 13)
                    )
                  )
                  (.zeroFace 10 1
                    (.exclude 13)
                  )
                )
              )
            )
            (.zeroFace 9 0
              (.split 2 (1667 / 10455)
                (.split 4 (1667 / 10455)
                  (.split 5 (1667 / 10455)
                    (.exclude 13)
                    (.zeroFace 10 0
                      (.exclude 13)
                    )
                  )
                  (.zeroFace 10 0
                    (.exclude 13)
                  )
                )
                (.zeroFace 10 3
                  (.exclude 13)
                )
              )
            )
          )
          (.zeroFace 9 3
            (.exclude 10)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 5 0
        (.exclude 9)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 6) (i6D1006LeafValid 2 2 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 6) root = 0 := by
  decide +kernel

end C099
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
