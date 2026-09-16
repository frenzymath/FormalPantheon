import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C051S010
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C051S010

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(180001 / 2000000), (180001 / 2000000), (180001 / 2000000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(410011 / 4000000), (410011 / 4000000), (309993 / 4000000)],
    ![(147503 / 1500000), (147503 / 1500000), (147503 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (80940161779200000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (107568709171200000 / 125067512150729))
              (.retain (107991754951680000 / 125067512150729))
            )
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (167603784330240000 / 125067512150729))
              (.retain (153743077647360000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (134153727022080000 / 125067512150729))
              (.retain (134661381995520000 / 125067512150729))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (193257187799040000 / 125067512150729))
              (.retain (207177126497280000 / 125067512150729))
            )
            (.retain (174306024000000000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (212822116024320000 / 125067512150729))
              (.retain (174056735370240000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (252670024028160000 / 125067512150729))
              (.retain (214136096209920000 / 125067512150729))
            )
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (169223645445120000 / 125067512150729))
              (.retain (208368471951360000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (214640879477760000 / 125067512150729))
              (.retain (215453185920000000 / 125067512150729))
            )
          )
          (.split 5 (1 / 2)
            (.retain (209062321113600000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (235168778603520000 / 125067512150729))
              (.retain (260260153989120000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (171223608867840000 / 125067512150729))
              (.retain (212537379225600000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (220552073948160000 / 125067512150729))
              (.retain (223143181240320000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.retain (209880249523200000 / 125067512150729))
            (.split 1 (1 / 2)
              (.retain (238033070760960000 / 125067512150729))
              (.retain (263384789806080000 / 125067512150729))
            )
          )
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (107213228328960000 / 125067512150729))
            (.retain (185444430888960000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (206166951452160000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (172688284339200000 / 125067512150729))
              (.retain (211525214330880000 / 125067512150729))
            )
          )
        )
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (133165771637760000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (204004788203520000 / 125067512150729))
              (.retain (267910325913600000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (249054982686720000 / 125067512150729))
              (.retain (210644358036480000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (280913600194560000 / 125067512150729))
              (.retain (7122310686720000 / 2908546794203))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (211958822154240000 / 125067512150729))
              (.retain (250556744079360000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (232897535953920000 / 125067512150729))
              (.retain (257592084433920000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (244701516856320000 / 125067512150729))
              (.retain (284368890147840000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (244192781445120000 / 125067512150729))
              (.retain (282561165941760000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (269260892974080000 / 125067512150729))
              (.retain (307386411402240000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (269813866199040000 / 125067512150729))
              (.retain (309328019435520000 / 125067512150729))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (262215751910400000 / 125067512150729))
              (.retain (300308598144000000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (331928763448320000 / 125067512150729))
              (.retain (357087540464640000 / 125067512150729))
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 5) (i6D1006LeafValid 2 0 5) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5) root = (59129121163 / 20000000000000) := by
  decide +kernel

end C051S010
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
