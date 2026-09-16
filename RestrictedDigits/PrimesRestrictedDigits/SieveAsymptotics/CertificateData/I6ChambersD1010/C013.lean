import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C013
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C013

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
    (.split 2 (34999 / 115005)
      (.split 4 (34999 / 115005)
        (.split 5 (34999 / 115005)
          (.zeroFace 3 0
            (.split 0 (185003 / 320024)
              (.split 3 (45007 / 80006)
                (.exclude 9)
                (.split 4 (135021 / 320024)
                  (.exclude 9)
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
              )
              (.exclude 9)
            )
          )
          (.split 0 (185003 / 320024)
            (.split 3 (45007 / 80006)
              (.exclude 9)
              (.split 4 (45007 / 80006)
                (.exclude 9)
                (.zeroFace 6 0
                  (.exclude 9)
                )
              )
            )
            (.exclude 9)
          )
        )
        (.split 0 (185003 / 425021)
          (.split 3 (80006 / 115005)
            (.split 5 (34999 / 80006)
              (.zeroFace 6 0
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.split 2 (185003 / 320024)
            (.split 5 (34999 / 80006)
              (.zeroFace 6 0
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
        )
      )
      (.split 0 (36667 / 76670)
        (.split 3 (80006 / 115005)
          (.exclude 9)
          (.split 4 (240018 / 425021)
            (.exclude 9)
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
        )
        (.exclude 9)
      )
    )
    (.zeroFace 0 1
      (.split 1 (80006 / 115005)
        (.split 3 (80006 / 115005)
          (.exclude 9)
          (.split 4 (40003 / 76670)
            (.exclude 9)
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
        )
        (.split 2 (40003 / 76670)
          (.split 4 (40003 / 76670)
            (.exclude 9)
            (.zeroFace 6 0
              (.exclude 9)
            )
          )
          (.zeroFace 6 2
            (.exclude 9)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 1) (i6D1006LeafValid 0 6 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 1) root = 0 := by
  decide +kernel

end C013
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
