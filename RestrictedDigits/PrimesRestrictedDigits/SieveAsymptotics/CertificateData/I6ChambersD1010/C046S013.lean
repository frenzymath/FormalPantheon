import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S013
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S013

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(23001 / 200000), (16249 / 250000), (16249 / 250000)],
    ![(280019 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 5 (1 / 2)
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (162152328683520000 / 125067512150729))
              (.retain (107942347868160000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (104905902827520000 / 125067512150729))
              (.retain (105985150494720000 / 125067512150729))
            )
          )
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (76829435351040000 / 125067512150729))
              (.retain (75990020474880000 / 125067512150729))
            )
            (.retain (47015990415360000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (166152886917120000 / 125067512150729))
              (.retain (110711965102080000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (106257703065600000 / 125067512150729))
              (.retain (110106567966720000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.retain (65671603814400000 / 125067512150729))
            (.retain (67193932339200000 / 125067512150729))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (45493452610560000 / 125067512150729))
            (.retain (15381495413760000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (31307286021120000 / 125067512150729))
            (.retain (32922453672960000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (46073243535360000 / 125067512150729))
            (.retain (15775686574080000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (31492964275200000 / 125067512150729))
            (.retain (33108131927040000 / 125067512150729))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (157718127605760000 / 125067512150729))
              (.retain (102848847790080000 / 125067512150729))
            )
            (.retain (68806211665920000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (35846474572800000 / 125067512150729))
            (.retain (36214854466560000 / 125067512150729))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (154025304637440000 / 125067512150729))
              (.retain (100386965790720000 / 125067512150729))
            )
            (.retain (66959800166400000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (32489590579200000 / 125067512150729))
            (.retain (34244361569280000 / 125067512150729))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (162841880954880000 / 125067512150729))
              (.retain (106264683356160000 / 125067512150729))
            )
            (.retain (75395091778560000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (37859976284160000 / 125067512150729))
            (.retain (38228356193280000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (169774736148480000 / 125067512150729))
              (.retain (110886586798080000 / 125067512150729))
            )
            (.retain (78861519375360000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (41927732536320000 / 125067512150729))
            (.retain (44545812157440000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (27587327381 / 20000000000000) := by
  decide +kernel

end C046S013
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
