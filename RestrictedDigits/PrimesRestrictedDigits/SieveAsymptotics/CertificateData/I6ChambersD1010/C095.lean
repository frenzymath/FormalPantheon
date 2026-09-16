import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C095
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C095

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
    (.split 2 (2576 / 3485)
      (.split 4 (2576 / 3485)
        (.split 5 (2576 / 3485)
          (.zeroFace 1 0
            (.zeroFace 4 1
              (.zeroFace 5 0
                (.exclude 13)
              )
            )
          )
          (.zeroFace 4 1
            (.zeroFace 5 0
              (.exclude 13)
            )
          )
        )
        (.zeroFace 4 1
          (.zeroFace 5 0
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 2 (18751 / 21252)
                    (.split 4 (18751 / 21252)
                      (.split 5 (18751 / 21252)
                        (.zeroFace 13 0
                          (.retain 138)
                        )
                        (.retain 396)
                      )
                      (.retain 656)
                    )
                    (.retain 916)
                  )
                  (.zeroFace 9 0
                    (.retain 1177)
                  )
                )
                (.zeroFace 9 0
                  (.retain 1177)
                )
              )
              (.zeroFace 9 3
                (.retain 1177)
              )
            )
          )
        )
      )
      (.zeroFace 4 1
        (.zeroFace 5 0
          (.exclude 9)
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 4 0
        (.zeroFace 5 0
          (.exclude 9)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 6) (i6D1006LeafValid 2 0 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 6) root = 0 := by
  decide +kernel

end C095
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
