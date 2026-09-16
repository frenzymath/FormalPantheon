import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C003

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

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
    (.split 0 (37501 / 115005)
      (.split 3 (310016 / 345015)
        (.split 2 (34999 / 115005)
          (.split 4 (34999 / 115005)
            (.split 5 (34999 / 115005)
              (.exclude 9)
              (.zeroFace 8 0
                (.exclude 9)
              )
            )
            (.zeroFace 8 0
              (.exclude 9)
            )
          )
          (.zeroFace 8 3
            (.exclude 9)
          )
        )
        (.split 4 (310016 / 575025)
          (.split 0 (174995 / 310016)
            (.split 3 (135021 / 310016)
              (.split 5 (34999 / 115005)
                (.exclude 9)
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.exclude 9)
            )
            (.split 2 (34999 / 115005)
              (.split 5 (34999 / 115005)
                (.exclude 9)
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.zeroFace 8 1
                (.exclude 9)
              )
            )
          )
          (.zeroFace 6 0
            (.split 2 (174995 / 310016)
              (.split 4 (174995 / 310016)
                (.split 5 (174995 / 310016)
                  (.exclude 9)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                )
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.zeroFace 8 3
                (.exclude 9)
              )
            )
          )
        )
      )
      (.split 2 (34999 / 115005)
        (.split 4 (34999 / 115005)
          (.split 5 (34999 / 115005)
            (.exclude 9)
            (.zeroFace 8 0
              (.exclude 9)
            )
          )
          (.zeroFace 8 0
            (.exclude 9)
          )
        )
        (.zeroFace 8 3
          (.exclude 9)
        )
      )
    )
    (.zeroFace 0 1
      (.split 1 (310016 / 345015)
        (.split 3 (310016 / 345015)
          (.exclude 8)
          (.split 4 (77504 / 115005)
            (.exclude 8)
            (.zeroFace 6 0
              (.exclude 8)
            )
          )
        )
        (.split 2 (77504 / 115005)
          (.split 4 (77504 / 115005)
            (.exclude 8)
            (.zeroFace 6 0
              (.exclude 8)
            )
          )
          (.zeroFace 6 2
            (.exclude 8)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 1) (i6D1006LeafValid 0 1 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1) root = 0 := by
  decide +kernel

end C003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
