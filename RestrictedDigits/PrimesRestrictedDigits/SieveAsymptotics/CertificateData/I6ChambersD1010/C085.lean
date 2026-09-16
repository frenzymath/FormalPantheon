import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C085
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C085

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

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
    (.split 0 (32498 / 115005)
      (.split 4 (82507 / 115005)
        (.split 5 (50009 / 115005)
          (.zeroFace 1 0
            (.zeroFace 12 2
              (.retain 0)
            )
          )
          (.split 3 (82507 / 132516)
            (.split 5 (1 / 2)
              (.zeroFace 12 2
                (.retain 631)
              )
              (.zeroFace 9 0
                (.zeroFace 12 3
                  (.retain 828)
                )
              )
            )
            (.zeroFace 12 3
              (.retain 0)
            )
          )
        )
        (.split 4 (2 / 3)
          (.split 5 (50009 / 132516)
            (.exclude 12)
            (.zeroFace 9 0
              (.exclude 12)
            )
          )
          (.zeroFace 9 0
            (.exclude 12)
          )
        )
      )
      (.split 1 (64996 / 115005)
        (.split 5 (50009 / 115005)
          (.zeroFace 1 0
            (.zeroFace 12 0
              (.retain 0)
            )
          )
          (.split 5 (1 / 2)
            (.zeroFace 12 0
              (.retain 184)
            )
            (.zeroFace 9 0
              (.zeroFace 12 0
                (.retain 167)
              )
            )
          )
        )
        (.zeroFace 1 1
          (.zeroFace 12 2
            (.retain 0)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 2 (82507 / 115005)
        (.split 4 (82507 / 115005)
          (.split 5 (50009 / 115005)
            (.zeroFace 1 0
              (.zeroFace 12 2
                (.retain 0)
              )
            )
            (.zeroFace 9 0
              (.zeroFace 12 3
                (.retain 0)
              )
            )
          )
          (.zeroFace 9 0
            (.exclude 12)
          )
        )
        (.zeroFace 9 3
          (.exclude 12)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 4) (i6D1006LeafValid 2 2 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 4) root = 0 := by
  decide +kernel

end C085
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
