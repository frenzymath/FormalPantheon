import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C018
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C018

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, false]))

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
          (.split 4 (8788 / 14849)
            (.split 2 (162511 / 242517)
              (.split 4 (800086063 / 1394090610)
                (.split 5 (93339 / 133342)
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
        (.split 4 (18334 / 24395)
          (.split 5 (8788 / 14849)
            (.split 2 (162511 / 242517)
              (.split 4 (120005 / 400026)
                (.split 5 (800086063 / 1394090610)
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
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
      )
      (.split 0 (379 / 27880)
        (.split 4 (18334 / 24395)
          (.split 2 (1669 / 2541)
            (.split 4 (120005 / 400026)
              (.split 5 (162511 / 242517)
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
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
        (.split 2 (75002 / 115005)
          (.split 4 (1669 / 2541)
            (.split 5 (162511 / 242517)
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
    (.zeroFace 0 1
      (.split 1 (4773 / 6970)
        (.split 3 (4773 / 6970)
          (.split 5 (6591 / 6970)
            (.split 2 (13182 / 13561)
              (.split 4 (13182 / 13561)
                (.exclude 9)
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
              (.zeroFace 6 2
                (.exclude 9)
              )
            )
            (.zeroFace 5 0
              (.zeroFace 6 3
                (.exclude 9)
              )
            )
          )
          (.split 2 (13182 / 13561)
            (.split 4 (27501 / 27880)
              (.split 5 (13182 / 13561)
                (.exclude 9)
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
            (.zeroFace 6 3
              (.exclude 9)
            )
          )
        )
        (.split 2 (27501 / 27880)
          (.split 4 (27501 / 27880)
            (.split 5 (13182 / 13561)
              (.exclude 9)
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.zeroFace 6 3
            (.exclude 9)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 1) (i6D1006LeafValid 1 1 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1) root = 0 := by
  decide +kernel

end C018
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
