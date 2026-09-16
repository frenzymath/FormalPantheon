import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C118S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C118S000

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, false]))

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
  (.split 0 (379 / 27880)
    (.split 4 (18334 / 24395)
      (.split 5 (4394 / 10455)
        (.split 0 (2653 / 27501)
          (.split 3 (18636 / 30305)
            (.split 5 (6668 / 30305)
              (.zeroFace 15 0
                (.retain 0)
              )
              (.zeroFace 9 0
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
            )
            (.zeroFace 15 0
              (.retain 0)
            )
          )
          (.split 2 (379 / 8258)
            (.split 5 (6668 / 30305)
              (.split 1 (11485595 / 216680379)
                (.zeroFace 15 0
                  (.retain 20)
                )
                (.split 2 (2297119 / 82374945)
                  (.zeroFace 15 0
                    (.retain 24)
                  )
                  (.retain (333057942274171696800000 / 16133497919450719227629))
                )
              )
              (.zeroFace 9 0
                (.split 2 (11485595 / 216680379)
                  (.split 5 (11485595 / 216680379)
                    (.zeroFace 15 0
                      (.retain 20)
                    )
                    (.retain 19)
                  )
                  (.retain 18)
                )
              )
            )
            (.zeroFace 9 1
              (.retain 6)
            )
          )
        )
        (.zeroFace 1 0
          (.split 0 (2653 / 27501)
            (.split 3 (24848 / 27501)
              (.zeroFace 9 0
                (.retain 0)
              )
              (.split 4 (18636 / 30305)
                (.zeroFace 9 0
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                )
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
            )
            (.zeroFace 9 1
              (.retain 0)
            )
          )
        )
      )
      (.zeroFace 1 0
        (.split 2 (2653 / 27501)
          (.split 4 (2653 / 27501)
            (.split 5 (2653 / 27501)
              (.zeroFace 15 0
                (.retain 0)
              )
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
      )
    )
    (.split 1 (379 / 6970)
      (.split 5 (4394 / 10455)
        (.split 2 (758 / 8637)
          (.split 4 (379 / 8258)
            (.split 5 (6668 / 30305)
              (.split 0 (10008696 / 27458315)
                (.split 3 (11485595 / 216680379)
                  (.zeroFace 15 0
                    (.retain 33)
                  )
                  (.split 4 (2297119 / 82374945)
                    (.zeroFace 15 0
                      (.retain 33)
                    )
                    (.retain (1042755946222458293256000000 / 35445294929033230143100913))
                  )
                )
                (.zeroFace 15 1
                  (.retain 35)
                )
              )
              (.zeroFace 9 0
                (.split 0 (10008696 / 27458315)
                  (.split 3 (17449619 / 27458315)
                    (.zeroFace 15 0
                      (.retain 35)
                    )
                    (.split 4 (11485595 / 216680379)
                      (.zeroFace 15 0
                        (.retain 33)
                      )
                      (.retain 30)
                    )
                  )
                  (.zeroFace 15 1
                    (.retain 35)
                  )
                )
              )
            )
            (.zeroFace 9 0
              (.split 2 (10008696 / 27458315)
                (.split 4 (10008696 / 27458315)
                  (.split 5 (10008696 / 27458315)
                    (.retain 32)
                    (.zeroFace 15 0
                      (.retain 35)
                    )
                  )
                  (.zeroFace 15 0
                    (.retain 35)
                  )
                )
                (.zeroFace 15 3
                  (.retain 35)
                )
              )
            )
          )
          (.zeroFace 9 3
            (.exclude 15)
          )
        )
        (.zeroFace 1 0
          (.exclude 9)
        )
      )
      (.split 2 (758 / 24395)
        (.split 4 (379 / 8258)
          (.split 5 (758 / 8637)
            (.split 1 (5758 / 7879)
              (.split 3 (17449619 / 27458315)
                (.zeroFace 15 0
                  (.retain 39)
                )
                (.split 4 (2297119 / 82374945)
                  (.zeroFace 15 0
                    (.retain 38)
                  )
                  (.retain (8839720028312128000000 / 268847267755242145189))
                )
              )
              (.split 2 (3032 / 70911)
                (.split 4 (2297119 / 82374945)
                  (.zeroFace 15 0
                    (.retain 46)
                  )
                  (.retain (160362971488123200000 / 4258703111473261253))
                )
                (.retain (21509518376220000 / 570908863856111))
              )
            )
            (.zeroFace 9 0
              (.split 2 (5758 / 7879)
                (.split 4 (17449619 / 27458315)
                  (.split 5 (5758 / 7879)
                    (.zeroFace 15 0
                      (.retain 39)
                    )
                    (.retain 38)
                  )
                  (.retain 33)
                )
                (.retain 33)
              )
            )
          )
          (.zeroFace 9 0
            (.retain 32)
          )
        )
        (.zeroFace 9 3
          (.retain 35)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 2 4 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = (29418063 / 100000000000000) := by
  decide +kernel

end C118S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
