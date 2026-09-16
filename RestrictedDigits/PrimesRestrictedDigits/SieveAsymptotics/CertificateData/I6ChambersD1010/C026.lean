import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C026
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C026

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
    (.split 4 (2 / 3)
      (.split 5 (1 / 2)
        (.split 0 (379 / 3485)
          (.split 3 (12424 / 17425)
            (.zeroFace 3 0
              (.zeroFace 15 0
                (.retain 0)
              )
            )
            (.split 4 (6212 / 24395)
              (.zeroFace 3 0
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
              (.zeroFace 15 0
                (.retain 0)
              )
            )
          )
          (.zeroFace 3 1
            (.retain 0)
          )
        )
        (.zeroFace 1 0
          (.split 0 (379 / 3485)
            (.split 3 (3106 / 3485)
              (.zeroFace 3 0
                (.retain 0)
              )
              (.split 4 (12424 / 17425)
                (.zeroFace 3 0
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                )
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
            )
            (.zeroFace 3 1
              (.retain 0)
            )
          )
        )
      )
      (.zeroFace 1 0
        (.split 2 (379 / 3485)
          (.split 4 (379 / 3485)
            (.split 5 (379 / 3485)
              (.zeroFace 15 0
                (.retain 0)
              )
              (.zeroFace 3 0
                (.retain 0)
              )
            )
            (.zeroFace 3 0
              (.retain 0)
            )
          )
          (.zeroFace 3 3
            (.retain 0)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 1 3
        (.exclude 3)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 0) (i6D1006LeafValid 1 4 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 0) root = 0 := by
  decide +kernel

end C026
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
