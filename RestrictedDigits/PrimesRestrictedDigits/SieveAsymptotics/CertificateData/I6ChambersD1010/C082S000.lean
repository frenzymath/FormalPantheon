import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C082S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C082S000

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (9546 / 17425)
    (.zeroFace 10 0
      (.exclude 12)
    )
    (.split 1 (479986 / 830049)
      (.split 3 (639998 / 890043)
        (.split 5 (5815 / 14652)
          (.zeroFace 12 0
            (.retain 350)
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.split 5 (1 / 2)
                (.split 4 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (4933946245606229644800000 / 7764021187568243479289))
                    (.retain (3237457800915642528000000 / 7764021187568243479289))
                  )
                  (.split 0 (1 / 2)
                    (.retain (3657102083387233528320000 / 7764021187568243479289))
                    (.retain (2762558540849949139200000 / 7764021187568243479289))
                  )
                )
                (.split 1 (1 / 2)
                  (.retain (2112687913654956697920000 / 7764021187568243479289))
                  (.retain (1939883420817217189440000 / 7764021187568243479289))
                )
              )
              (.split 0 (1 / 2)
                (.split 4 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (5131292826974283325440000 / 7764021187568243479289))
                    (.retain (4415368387680689967360000 / 7764021187568243479289))
                  )
                  (.split 3 (1 / 2)
                    (.retain (4229950403454861980160000 / 7764021187568243479289))
                    (.retain (4669675639644285177600000 / 7764021187568243479289))
                  )
                )
                (.split 5 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (4159125816920434375680000 / 7764021187568243479289))
                    (.retain (3161827553606324023680000 / 7764021187568243479289))
                  )
                  (.split 1 (1 / 2)
                    (.retain (3235899701609515167360000 / 7764021187568243479289))
                    (.retain (2382044714959920326400000 / 7764021187568243479289))
                  )
                )
              )
            )
            (.split 0 (1 / 2)
              (.split 3 (1 / 2)
                (.split 2 (1 / 2)
                  (.retain (3445567700675391560640000 / 7764021187568243479289))
                  (.retain (2357374025590084872000000 / 7764021187568243479289))
                )
                (.split 4 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (4837467723566413407360000 / 7764021187568243479289))
                    (.retain (3714447651893558737920000 / 7764021187568243479289))
                  )
                  (.split 0 (1 / 2)
                    (.retain (4395037251623379379200000 / 7764021187568243479289))
                    (.retain (3554825272957438798080000 / 7764021187568243479289))
                  )
                )
              )
              (.split 2 (1 / 2)
                (.split 4 (1 / 2)
                  (.retain (3435971658465516522240000 / 7764021187568243479289))
                  (.retain (2403738466470734198400000 / 7764021187568243479289))
                )
                (.split 1 (1 / 2)
                  (.retain (1415948865725564983680000 / 7764021187568243479289))
                  (.retain (1325603113570322260800000 / 7764021187568243479289))
                )
              )
            )
          )
        )
        (.zeroFace 12 0
          (.retain 160)
        )
      )
      (.zeroFace 12 2
        (.retain 35)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 0) (i6D1006LeafValid 2 2 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0) root = (3813789379 / 5000000000000) := by
  decide +kernel

end C082S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
