import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C077
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C077

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
    (.zeroFace 4 1
      (.split 2 (9546 / 17425)
        (.split 4 (9546 / 17425)
          (.split 5 (9546 / 17425)
            (.zeroFace 10 0
              (.exclude 12)
            )
            (.split 1 (639998 / 890043)
              (.split 3 (639998 / 890043)
                (.split 5 (5815 / 14652)
                  (.zeroFace 12 0
                    (.retain 738)
                  )
                  (.retain 642)
                )
                (.zeroFace 12 0
                  (.retain 699)
                )
              )
              (.zeroFace 12 2
                (.retain 699)
              )
            )
          )
          (.split 1 (639998 / 890043)
            (.split 3 (64996 / 115005)
              (.split 5 (250045 / 890043)
                (.zeroFace 12 0
                  (.retain 602)
                )
                (.retain 444)
              )
              (.zeroFace 12 0
                (.retain 602)
              )
            )
            (.zeroFace 12 2
              (.retain 699)
            )
          )
        )
        (.split 1 (64996 / 115005)
          (.split 3 (64996 / 115005)
            (.split 5 (250045 / 890043)
              (.zeroFace 12 0
                (.retain 253)
              )
              (.retain 248)
            )
            (.zeroFace 12 0
              (.retain 0)
            )
          )
          (.zeroFace 12 2
            (.retain 0)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 4 0
        (.split 1 (64996 / 115005)
          (.split 3 (64996 / 115005)
            (.split 5 (50009 / 115005)
              (.zeroFace 12 0
                (.retain 0)
              )
              (.retain 0)
            )
            (.zeroFace 12 0
              (.retain 0)
            )
          )
          (.zeroFace 12 2
            (.retain 0)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = 0 := by
  decide +kernel

end C077
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
