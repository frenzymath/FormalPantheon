import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S032
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S032

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1097517 / 8000000), (767489 / 8000000), (767489 / 8000000)],
    ![(672519 / 4000000), (342491 / 4000000), (342491 / 4000000)],
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (1 / 2)
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (524613775749120000 / 561658568377843))
              (.retain (435921003417600000 / 561658568377843))
            )
            (.retain (300781094584320000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (201743621775360000 / 561658568377843))
            (.retain (197047218677760000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (102312083865600000 / 561658568377843))
          (.retain (102897630581760000 / 561658568377843))
        )
      )
      (.split 5 (1 / 2)
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (386727535687680000 / 561658568377843))
            (.retain (201701132421120000 / 561658568377843))
          )
          (.retain (285201561139200000 / 561658568377843))
        )
        (.split 0 (1 / 2)
          (.retain (100094395484160000 / 561658568377843))
          (.retain (96694482447360000 / 561658568377843))
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (532080227266560000 / 561658568377843))
              (.retain (448521767608320000 / 561658568377843))
            )
            (.retain (307565036605440000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.retain (208033430722560000 / 561658568377843))
            (.retain (205769296281600000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (107603526528000000 / 561658568377843))
          (.retain (109567835136000000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (389533792204800000 / 561658568377843))
            (.retain (203384886405120000 / 561658568377843))
          )
          (.retain (287446566389760000 / 561658568377843))
        )
        (.split 1 (1 / 2)
          (.retain (102433032437760000 / 561658568377843))
          (.retain (99033119400960000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (69004165573 / 100000000000000) := by
  decide +kernel

end C059S032
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
