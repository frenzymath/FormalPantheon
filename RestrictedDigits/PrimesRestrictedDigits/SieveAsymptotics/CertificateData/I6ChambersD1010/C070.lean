import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C070
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C070

abbrev label : i6D691Label :=
  (true, (2, ![false, false, false, true, false]))

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
            (.exclude 11)
          )
          (.split 1 (1591 / 2879)
            (.split 3 (1 / 2)
              (.split 5 (1 / 2)
                (.exclude 11)
                (.zeroFace 9 0
                  (.exclude 11)
                )
              )
              (.exclude 11)
            )
            (.exclude 11)
          )
        )
        (.split 0 (1591 / 2879)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.exclude 11)
              (.zeroFace 9 0
                (.exclude 11)
              )
            )
            (.zeroFace 9 0
              (.exclude 11)
            )
          )
          (.split 1 (1591 / 2879)
            (.split 5 (1 / 2)
              (.exclude 11)
              (.zeroFace 9 0
                (.exclude 11)
              )
            )
            (.exclude 11)
          )
        )
      )
      (.split 2 (379 / 5152)
        (.split 4 (1288 / 2879)
          (.split 5 (1288 / 2879)
            (.split 0 (1091141 / 16633905)
              (.exclude 11)
              (.split 1 (1091141 / 16633905)
                (.exclude 11)
                (.split 2 (379 / 14319)
                  (.exclude 11)
                  (.zeroFace 10 1
                    (.exclude 11)
                  )
                )
              )
            )
            (.zeroFace 9 0
              (.split 0 (1091141 / 16633905)
                (.split 3 (15542764 / 16633905)
                  (.split 5 (1091141 / 16633905)
                    (.exclude 11)
                    (.zeroFace 10 0
                      (.exclude 11)
                    )
                  )
                  (.exclude 11)
                )
                (.split 2 (1091141 / 16633905)
                  (.split 5 (1091141 / 16633905)
                    (.exclude 11)
                    (.zeroFace 10 0
                      (.exclude 11)
                    )
                  )
                  (.zeroFace 10 1
                    (.exclude 11)
                  )
                )
              )
            )
          )
          (.zeroFace 9 0
            (.split 2 (1091141 / 16633905)
              (.split 4 (1091141 / 16633905)
                (.split 5 (1091141 / 16633905)
                  (.exclude 11)
                  (.zeroFace 10 0
                    (.exclude 11)
                  )
                )
                (.zeroFace 10 0
                  (.exclude 11)
                )
              )
              (.zeroFace 10 3
                (.exclude 11)
              )
            )
          )
        )
        (.zeroFace 9 3
          (.exclude 10)
        )
      )
    )
    (.zeroFace 0 1
      (.exclude 9)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 6) (i6D1006LeafValid 2 0 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 6) root = 0 := by
  decide +kernel

end C070
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
