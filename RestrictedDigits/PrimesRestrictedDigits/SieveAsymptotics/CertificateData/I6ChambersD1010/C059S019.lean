import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S019
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S019

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1592559 / 8000000), (24099 / 320000), (24099 / 320000)],
    ![(23001 / 100000), (16249 / 250000), (16249 / 250000)],
    ![(377513 / 2000000), (212499 / 2000000), (16249 / 250000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (778814758748160000 / 561658568377843))
                (.retain (678679254835200000 / 561658568377843))
              )
              (.retain (576424394588160000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (474635653263360000 / 561658568377843))
              (.retain (329388353187840000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.retain (262122454425600000 / 561658568377843))
            (.retain (256545839278080000 / 561658568377843))
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (807881093775360000 / 561658568377843))
                (.retain (770342155960320000 / 561658568377843))
              )
              (.retain (643884475576320000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (579848904806400000 / 561658568377843))
              (.retain (367615824814080000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (537588075847680000 / 561658568377843))
              (.retain (612942626672640000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (524853654036480000 / 561658568377843))
              (.retain (300162700247040000 / 561658568377843))
            )
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (818939579351040000 / 561658568377843))
                (.retain (783920647249920000 / 561658568377843))
              )
              (.retain (694567387054080000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (422524963123200000 / 561658568377843))
              (.retain (619348712509440000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (479307213434880000 / 561658568377843))
              (.retain (634993340497920000 / 561658568377843))
            )
            (.split 5 (1 / 2)
              (.retain (629519307264000000 / 561658568377843))
              (.retain (429789673635840000 / 561658568377843))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (245440571443200000 / 561658568377843))
            (.split 4 (1 / 2)
              (.retain (396875537510400000 / 561658568377843))
              (.retain (417134327316480000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (385277887918080000 / 561658568377843))
              (.retain (405536677724160000 / 561658568377843))
            )
            (.retain (249443001262080000 / 561658568377843))
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 0 (1 / 2)
            (.retain (282506461286400000 / 561658568377843))
            (.retain (269885204121600000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (94375991439360000 / 561658568377843))
            (.retain (96724205475840000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (181809309081600000 / 561658568377843))
            (.retain (190223480494080000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.retain (176812476272640000 / 561658568377843))
            (.retain (174988231004160000 / 561658568377843))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (298896097443840000 / 561658568377843))
            (.retain (295398724147200000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (108863905628160000 / 561658568377843))
            (.retain (113274134968320000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (193293906923520000 / 561658568377843))
            (.retain (190962324725760000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (185841146511360000 / 561658568377843))
            (.retain (177934312028160000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (22647777769 / 20000000000000) := by
  decide +kernel

end C059S019
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
