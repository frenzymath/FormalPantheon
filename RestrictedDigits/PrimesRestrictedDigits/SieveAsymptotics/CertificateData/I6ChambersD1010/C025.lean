import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C025
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C025

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
    (.split 1 (758 / 3485)
      (.split 3 (2576 / 3485)
        (.zeroFace 1 0
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
        (.split 4 (2576 / 3485)
          (.zeroFace 1 0
            (.split 0 (379 / 3864)
              (.split 3 (3485 / 3864)
                (.zeroFace 6 3
                  (.exclude 9)
                )
                (.split 4 (3485 / 3864)
                  (.zeroFace 6 3
                    (.exclude 9)
                  )
                  (.zeroFace 3 0
                    (.exclude 6)
                  )
                )
              )
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
          )
          (.split 0 (379 / 5152)
            (.split 3 (4773 / 5152)
              (.split 5 (379 / 3864)
                (.zeroFace 3 0
                  (.exclude 6)
                )
                (.exclude 6)
              )
              (.zeroFace 3 0
                (.exclude 6)
              )
            )
            (.split 2 (379 / 3864)
              (.split 5 (379 / 3864)
                (.zeroFace 3 0
                  (.exclude 6)
                )
                (.exclude 6)
              )
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
          )
        )
      )
      (.split 2 (758 / 3485)
        (.split 4 (2576 / 3485)
          (.zeroFace 1 0
            (.split 1 (2 / 3)
              (.split 3 (3485 / 3864)
                (.split 5 (1 / 3)
                  (.zeroFace 3 0
                    (.zeroFace 6 0
                      (.exclude 9)
                    )
                  )
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
                (.zeroFace 3 0
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
              )
              (.zeroFace 3 2
                (.exclude 9)
              )
            )
          )
          (.split 1 (2 / 3)
            (.split 3 (4773 / 5152)
              (.split 5 (379 / 3864)
                (.zeroFace 3 0
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
              (.zeroFace 3 0
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
            )
            (.zeroFace 3 2
              (.exclude 9)
            )
          )
        )
        (.split 1 (1 / 4)
          (.split 3 (4773 / 5152)
            (.split 5 (1 / 3)
              (.zeroFace 3 0
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
            (.zeroFace 3 0
              (.zeroFace 6 0
                (.exclude 9)
              )
            )
          )
          (.zeroFace 3 2
            (.exclude 9)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 1 (2576 / 3485)
        (.split 3 (2576 / 3485)
          (.split 5 (2727 / 3485)
            (.split 2 (3 / 4)
              (.split 4 (3 / 4)
                (.split 5 (3 / 4)
                  (.zeroFace 3 0
                    (.zeroFace 6 2
                      (.exclude 9)
                    )
                  )
                  (.zeroFace 6 2
                    (.exclude 9)
                  )
                )
                (.zeroFace 6 2
                  (.exclude 9)
                )
              )
              (.zeroFace 6 2
                (.exclude 9)
              )
            )
            (.zeroFace 1 0
              (.zeroFace 6 3
                (.exclude 9)
              )
            )
          )
          (.split 0 (379 / 5152)
            (.split 3 (4773 / 5152)
              (.split 5 (3 / 4)
                (.zeroFace 3 0
                  (.exclude 6)
                )
                (.exclude 6)
              )
              (.zeroFace 3 0
                (.exclude 6)
              )
            )
            (.split 2 (3 / 4)
              (.split 5 (3 / 4)
                (.zeroFace 3 0
                  (.exclude 6)
                )
                (.exclude 6)
              )
              (.exclude 6)
            )
          )
        )
        (.split 1 (4773 / 5152)
          (.split 3 (4773 / 5152)
            (.split 5 (3 / 4)
              (.zeroFace 3 0
                (.exclude 6)
              )
              (.exclude 6)
            )
            (.zeroFace 3 0
              (.exclude 6)
            )
          )
          (.zeroFace 3 2
            (.exclude 6)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 1 3 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = 0 := by
  decide +kernel

end C025
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
