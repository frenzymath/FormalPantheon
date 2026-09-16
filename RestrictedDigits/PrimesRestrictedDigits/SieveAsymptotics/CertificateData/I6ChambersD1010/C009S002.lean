import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C009S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C009S002

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(287501 / 1000000), (72501 / 1000000), (16249 / 250000)],
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
            let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1501 / 23001));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
                   let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1501 / 23001));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (1501 / 30668)
    (.split 4 (1501 / 30668)
      (.split 2 (287501 / 437505)
        (.split 4 (287501 / 437505)
          (.split 5 (287501 / 437505)
            (.zeroFace 3 0
              (.exclude 8)
            )
            (.split 1 (69998 / 287501)
              (.split 3 (69998 / 287501)
                (.split 5 (217503 / 287501)
                  (.zeroFace 8 0
                    (.exclude 9)
                  )
                  (.exclude 9)
                )
                (.zeroFace 8 0
                  (.exclude 9)
                )
              )
              (.zeroFace 8 2
                (.exclude 9)
              )
            )
          )
          (.split 0 (69998 / 287501)
            (.split 4 (217503 / 287501)
              (.split 5 (217503 / 287501)
                (.zeroFace 8 0
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.split 1 (69998 / 287501)
              (.split 5 (217503 / 287501)
                (.zeroFace 8 0
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.zeroFace 8 1
                (.exclude 9)
              )
            )
          )
        )
        (.split 2 (217503 / 287501)
          (.split 4 (217503 / 287501)
            (.split 5 (217503 / 287501)
              (.zeroFace 8 0
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.exclude 9)
        )
      )
      (.zeroFace 1 0
        (.exclude 9)
      )
    )
    (.zeroFace 1 2
      (.exclude 9)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 0 4 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = 0 := by
  decide +kernel

end C009S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
