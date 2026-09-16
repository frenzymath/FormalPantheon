import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C103S012
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C103S012

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(37501 / 250000), (37501 / 250000), (12499 / 100000)],
    ![(37501 / 250000), (37501 / 250000), (37501 / 250000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 3485));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 3485));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (1 / 4)
    (.split 4 (1288 / 1667)
      (.split 5 (1 / 2)
        (.split 0 (1667 / 10455)
          (.exclude 13)
          (.split 1 (1 / 3)
            (.exclude 13)
            (.split 2 (1 / 9)
              (.exclude 13)
              (.zeroFace 10 1
                (.exclude 13)
              )
            )
          )
        )
        (.zeroFace 9 0
          (.split 0 (1667 / 10455)
            (.split 3 (8788 / 10455)
              (.split 5 (1 / 3)
                (.exclude 13)
                (.zeroFace 10 0
                  (.exclude 13)
                )
              )
              (.exclude 13)
            )
            (.split 2 (1 / 3)
              (.split 5 (1 / 3)
                (.exclude 13)
                (.zeroFace 10 0
                  (.exclude 13)
                )
              )
              (.zeroFace 10 1
                (.exclude 13)
              )
            )
          )
        )
      )
      (.zeroFace 9 0
        (.split 2 (1667 / 10455)
          (.split 4 (1667 / 10455)
            (.split 5 (1667 / 10455)
              (.exclude 13)
              (.zeroFace 10 0
                (.exclude 13)
              )
            )
            (.zeroFace 10 0
              (.exclude 13)
            )
          )
          (.zeroFace 10 3
            (.exclude 13)
          )
        )
      )
    )
    (.zeroFace 9 3
      (.exclude 10)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 2 3 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = 0 := by
  decide +kernel

end C103S012
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
