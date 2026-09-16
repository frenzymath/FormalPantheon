import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C019S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C019S001

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(54167 / 375000), (54167 / 375000), (54167 / 375000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 10455));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 10455));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (379 / 6970)
    (.split 3 (4773 / 6970)
      (.split 5 (19773 / 22805)
        (.split 4 (19773 / 21289)
          (.split 2 (9 / 11)
            (.split 4 (26595 / 47884)
              (.split 5 (72963 / 95768)
                (.retain (114135140614450000 / 31795313690482771))
                (.zeroFace 9 0
                  (.retain 7)
                )
              )
              (.zeroFace 9 0
                (.retain 9)
              )
            )
            (.zeroFace 9 3
              (.retain 11)
            )
          )
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
        (.zeroFace 5 0
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
      )
      (.split 4 (82503 / 85535)
        (.split 5 (19773 / 21289)
          (.split 2 (9 / 11)
            (.split 4 (10233 / 95768)
              (.split 5 (26595 / 47884)
                (.retain (743981412535600000 / 207226716765599817))
                (.zeroFace 9 0
                  (.retain 7)
                )
              )
              (.zeroFace 9 0
                (.retain 9)
              )
            )
            (.zeroFace 9 3
              (.retain 11)
            )
          )
          (.zeroFace 6 0
            (.exclude 9)
          )
        )
        (.zeroFace 6 0
          (.exclude 9)
        )
      )
    )
    (.split 0 (379 / 27880)
      (.split 4 (82503 / 85535)
        (.split 2 (27 / 35)
          (.split 4 (10233 / 95768)
            (.split 5 (9 / 11)
              (.retain (106531126100000 / 16468680386829))
              (.zeroFace 9 0
                (.retain 10)
              )
            )
            (.zeroFace 9 0
              (.retain 11)
            )
          )
          (.zeroFace 9 3
            (.retain 14)
          )
        )
        (.zeroFace 6 0
          (.exclude 9)
        )
      )
      (.split 2 (3 / 4)
        (.split 4 (27 / 35)
          (.split 5 (9 / 11)
            (.retain (63598500000 / 6587232619))
            (.zeroFace 9 0
              (.retain 14)
            )
          )
          (.zeroFace 9 0
            (.retain 15)
          )
        )
        (.zeroFace 9 3
          (.retain 15)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 6) (i6D1006LeafValid 1 1 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 6) root = (704161 / 50000000000000) := by
  decide +kernel

end C019S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
