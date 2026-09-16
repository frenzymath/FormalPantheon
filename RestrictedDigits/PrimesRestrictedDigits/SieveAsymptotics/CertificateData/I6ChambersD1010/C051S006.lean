import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C051S006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C051S006

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(24689 / 187500), (244997 / 3000000), (244997 / 3000000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (13848543313920000 / 125067512150729))
            (.retain (14038371601920000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (28198277936640000 / 125067512150729))
            (.retain (1320368970240000 / 2908546794203))
          )
        )
        (.split 1 (1 / 2)
          (.retain (340594721280000 / 2908546794203))
          (.split 2 (1 / 2)
            (.retain (28739566725120000 / 125067512150729))
            (.retain (57678013693440000 / 125067512150729))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (13841556779520000 / 125067512150729))
            (.retain (326311280640000 / 2908546794203))
          )
          (.split 0 (1 / 2)
            (.retain (28156708385280000 / 125067512150729))
            (.retain (56729871590400000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.retain (14505441281280000 / 125067512150729))
          (.split 2 (1 / 2)
            (.retain (28594412720640000 / 125067512150729))
            (.retain (57459378839040000 / 125067512150729))
          )
        )
      )
    )
    (.split 2 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (27509243143680000 / 125067512150729))
            (.retain (54939328473600000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (84044244648960000 / 125067512150729))
              (.retain (82960403880960000 / 125067512150729))
            )
            (.retain (55385676195840000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (57050700871680000 / 125067512150729))
            (.retain (28743080762880000 / 125067512150729))
          )
          (.split 5 (1 / 2)
            (.retain (55800278231040000 / 125067512150729))
            (.split 1 (1 / 2)
              (.retain (84624687498240000 / 125067512150729))
              (.retain (83540846730240000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (104623987737600000 / 125067512150729))
              (.retain (119794035824640000 / 125067512150729))
            )
            (.retain (113712731066880000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (91105602186240000 / 125067512150729))
              (.retain (106222657628160000 / 125067512150729))
            )
            (.retain (71963802616320000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (117960956743680000 / 125067512150729))
              (.retain (133177208094720000 / 125067512150729))
            )
            (.retain (99628422543360000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (163351775646720000 / 125067512150729))
            (.retain (121867947671040000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 5) (i6D1006LeafValid 2 0 5) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5) root = (78575272729 / 100000000000000) := by
  decide +kernel

end C051S006
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
