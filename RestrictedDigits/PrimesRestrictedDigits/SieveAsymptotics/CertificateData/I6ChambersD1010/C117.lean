import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C117
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C117

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
    (.split 4 (2 / 3)
      (.split 5 (1 / 2)
        (.split 0 (379 / 3485)
          (.split 3 (12424 / 17425)
            (.split 5 (1667 / 17425)
              (.zeroFace 10 0
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
              (.zeroFace 15 0
                (.retain 0)
              )
            )
            (.zeroFace 10 0
              (.zeroFace 15 0
                (.retain 0)
              )
            )
          )
          (.split 2 (758 / 24395)
            (.split 5 (1667 / 17425)
              (.zeroFace 10 0
                (.split 1 (1895 / 23637)
                  (.split 5 (21742 / 23637)
                    (.retain 29)
                    (.zeroFace 15 0
                      (.retain 30)
                    )
                  )
                  (.retain 28)
                )
              )
              (.split 1 (758 / 7121)
                (.zeroFace 15 0
                  (.retain 23)
                )
                (.split 2 (1895 / 23637)
                  (.zeroFace 15 0
                    (.retain 28)
                  )
                  (.retain (3167716535130000 / 120790084534603))
                )
              )
            )
            (.split 1 (758 / 3485)
              (.split 5 (6363 / 7121)
                (.retain (3210158763280000 / 197597216872143))
                (.zeroFace 15 0
                  (.retain 8)
                )
              )
              (.retain (625824850000 / 72459558809))
            )
          )
        )
        (.zeroFace 1 0
          (.split 0 (379 / 3485)
            (.split 3 (3106 / 3485)
              (.split 5 (758 / 3485)
                (.zeroFace 15 0
                  (.retain 0)
                )
                (.retain 0)
              )
              (.split 4 (12424 / 17425)
                (.zeroFace 15 0
                  (.retain 0)
                )
                (.zeroFace 10 0
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                )
              )
            )
            (.split 2 (758 / 3485)
              (.split 5 (758 / 3485)
                (.zeroFace 15 0
                  (.retain 0)
                )
                (.retain 0)
              )
              (.retain 0)
            )
          )
        )
      )
      (.zeroFace 1 0
        (.split 2 (379 / 3485)
          (.split 4 (379 / 3485)
            (.split 5 (379 / 3485)
              (.zeroFace 10 0
                (.retain 0)
              )
              (.retain 0)
            )
            (.retain 0)
          )
          (.retain 0)
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 1 3
        (.retain 0)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 0) (i6D1006LeafValid 2 4 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 0) root = (37115637 / 100000000000000) := by
  decide +kernel

end C117
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
