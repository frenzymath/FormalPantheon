import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S016
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S016

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(377513 / 2000000), (212499 / 2000000), (16249 / 250000)],
    ![(147503 / 1000000), (147503 / 1000000), (16249 / 250000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (1 / 2)
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (778176795525120000 / 561658568377843))
                (.retain (723792046325760000 / 561658568377843))
              )
              (.retain (598940665712640000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (533032888688640000 / 561658568377843))
              (.retain (338870473482240000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (530707629957120000 / 561658568377843))
              (.retain (478011893760000000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (471807085916160000 / 561658568377843))
              (.retain (270197887979520000 / 561658568377843))
            )
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (759893687377920000 / 561658568377843))
                (.retain (662510575042560000 / 561658568377843))
              )
              (.retain (549901774725120000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (453128157757440000 / 561658568377843))
              (.retain (307505583636480000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.retain (253526878863360000 / 561658568377843))
            (.retain (243208203448320000 / 561658568377843))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (788311711457280000 / 561658568377843))
                (.retain (735745011425280000 / 561658568377843))
              )
              (.retain (643698173214720000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (567712424448000000 / 561658568377843))
              (.retain (388227888967680000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (548418918481920000 / 561658568377843))
              (.retain (424609095536640000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (562708904878080000 / 561658568377843))
              (.retain (384653946470400000 / 561658568377843))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (346844289208320000 / 561658568377843))
              (.retain (355856493957120000 / 561658568377843))
            )
            (.retain (217638858516480000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (335803086766080000 / 561658568377843))
              (.retain (344815291514880000 / 561658568377843))
            )
            (.retain (209274239139840000 / 561658568377843))
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 0 (1 / 2)
            (.retain (239583265873920000 / 561658568377843))
            (.retain (230746207242240000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (83671680983040000 / 561658568377843))
            (.retain (84035512995840000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (156244073794560000 / 561658568377843))
          (.retain (146772455731200000 / 561658568377843))
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (243353281536000000 / 561658568377843))
            (.retain (236586961336320000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (86826987786240000 / 561658568377843))
            (.retain (88011106191360000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (157624566082560000 / 561658568377843))
          (.retain (148152948019200000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (100519585563 / 100000000000000) := by
  decide +kernel

end C059S016
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
