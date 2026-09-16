import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C017
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C017

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
    (.split 2 (758 / 24395)
      (.split 4 (9546 / 17425)
        (.split 5 (9546 / 17425)
          (.split 0 (1895 / 23637)
            (.split 3 (6212 / 7879)
              (.split 2 (70833 / 110836)
                (.split 4 (319999 / 520014)
                  (.split 5 (319999 / 520014)
                    (.zeroFace 10 0
                      (.exclude 15)
                    )
                    (.exclude 15)
                  )
                  (.exclude 15)
                )
                (.zeroFace 15 0
                  (.retain 0)
                )
              )
              (.split 4 (24848 / 55153)
                (.split 2 (70833 / 110836)
                  (.split 4 (120005 / 400026)
                    (.split 5 (319999 / 520014)
                      (.zeroFace 10 0
                        (.exclude 15)
                      )
                      (.exclude 15)
                    )
                    (.exclude 15)
                  )
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                )
                (.zeroFace 6 0
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                )
              )
            )
            (.split 2 (500000 / 780021)
              (.split 4 (70833 / 110836)
                (.split 5 (319999 / 520014)
                  (.zeroFace 10 0
                    (.exclude 15)
                  )
                  (.exclude 15)
                )
                (.zeroFace 15 1
                  (.retain 0)
                )
              )
              (.split 1 (1895 / 23637)
                (.zeroFace 15 0
                  (.retain 0)
                )
                (.split 2 (37521 / 1000000)
                  (.zeroFace 15 0
                    (.retain 8)
                  )
                  (.retain (266100800000 / 72459558809))
                )
              )
            )
          )
          (.zeroFace 1 0
            (.split 0 (1895 / 23637)
              (.split 3 (21742 / 23637)
                (.split 5 (1895 / 23637)
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                  (.retain 0)
                )
                (.split 4 (6212 / 7879)
                  (.zeroFace 15 0
                    (.retain 0)
                  )
                  (.zeroFace 6 0
                    (.zeroFace 15 0
                      (.retain 0)
                    )
                  )
                )
              )
              (.split 2 (1895 / 23637)
                (.split 5 (1895 / 23637)
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
          (.split 2 (1895 / 23637)
            (.split 4 (1895 / 23637)
              (.split 5 (1895 / 23637)
                (.zeroFace 6 0
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
      (.zeroFace 1 3
        (.retain 0)
      )
    )
    (.zeroFace 0 1
      (.exclude 1)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 0) (i6D1006LeafValid 1 1 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0) root = (23759 / 1250000000000) := by
  decide +kernel

end C017
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
