import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C115
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C115

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
    (.split 1 (379 / 6970)
      (.split 3 (4773 / 6970)
        (.split 5 (4394 / 10455)
          (.zeroFace 6 0
            (.split 2 (758 / 8637)
              (.split 4 (758 / 8637)
                (.split 5 (6668 / 30305)
                  (.exclude 15)
                  (.zeroFace 9 0
                    (.exclude 15)
                  )
                )
                (.zeroFace 9 0
                  (.exclude 15)
                )
              )
              (.zeroFace 9 3
                (.exclude 15)
              )
            )
          )
          (.zeroFace 1 0
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
        )
        (.zeroFace 6 0
          (.split 2 (758 / 8637)
            (.split 4 (758 / 8637)
              (.split 5 (758 / 8637)
                (.exclude 15)
                (.zeroFace 9 0
                  (.exclude 15)
                )
              )
              (.zeroFace 9 0
                (.exclude 15)
              )
            )
            (.zeroFace 9 3
              (.exclude 15)
            )
          )
        )
      )
      (.zeroFace 6 0
        (.split 2 (758 / 24395)
          (.split 4 (758 / 24395)
            (.split 5 (758 / 8637)
              (.split 1 (5758 / 7879)
                (.split 3 (5758 / 7879)
                  (.zeroFace 15 0
                    (.retain 41)
                  )
                  (.split 4 (3032 / 70911)
                    (.zeroFace 15 0
                      (.retain 44)
                    )
                    (.retain 43)
                  )
                )
                (.split 2 (3032 / 70911)
                  (.split 4 (3032 / 70911)
                    (.zeroFace 15 0
                      (.retain 51)
                    )
                    (.retain 46)
                  )
                  (.retain 41)
                )
              )
              (.zeroFace 9 0
                (.split 2 (5758 / 7879)
                  (.split 4 (5758 / 7879)
                    (.split 5 (5758 / 7879)
                      (.zeroFace 15 0
                        (.retain 41)
                      )
                      (.retain 39)
                    )
                    (.retain 38)
                  )
                  (.retain 37)
                )
              )
            )
            (.zeroFace 9 0
              (.retain 35)
            )
          )
          (.zeroFace 9 3
            (.retain 35)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 1 (4773 / 6970)
        (.split 3 (4773 / 6970)
          (.split 5 (6591 / 6970)
            (.zeroFace 6 2
              (.exclude 9)
            )
            (.zeroFace 1 0
              (.zeroFace 6 3
                (.exclude 9)
              )
            )
          )
          (.zeroFace 6 3
            (.exclude 9)
          )
        )
        (.zeroFace 6 3
          (.exclude 9)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 1) (i6D1006LeafValid 2 3 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 1) root = 0 := by
  decide +kernel

end C115
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
