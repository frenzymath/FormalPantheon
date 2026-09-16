import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C051S009
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C051S009

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(410011 / 4000000), (410011 / 4000000), (309993 / 4000000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (1 / 2)
    (.split 5 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (40959497410560000 / 125067512150729))
            (.retain (41151455815680000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (75158105402880000 / 125067512150729))
            (.retain (115516307197440000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (69540775626240000 / 125067512150729))
            (.split 4 (1 / 2)
              (.retain (90321521356800000 / 125067512150729))
              (.retain (105277252561920000 / 125067512150729))
            )
          )
          (.split 2 (1 / 2)
            (.retain (89493062100480000 / 125067512150729))
            (.retain (130008546823680000 / 125067512150729))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (42984325555200000 / 125067512150729))
            (.retain (43666747614720000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.retain (56947490357760000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (85852116357120000 / 125067512150729))
              (.retain (85549243438080000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (84040196889600000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (112351702671360000 / 125067512150729))
              (.retain (2621634739200000 / 2908546794203))
            )
          )
          (.split 4 (1 / 2)
            (.retain (103816557388800000 / 125067512150729))
            (.retain (144865223101440000 / 125067512150729))
          )
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (54457502630400000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (81705241774080000 / 125067512150729))
              (.retain (81366805186560000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (108193703224320000 / 125067512150729))
              (.retain (108616749004800000 / 125067512150729))
            )
            (.retain (135129018908160000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (104598605030400000 / 125067512150729))
              (.retain (116613683020800000 / 125067512150729))
            )
            (.retain (109404593072640000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (118340049899520000 / 125067512150729))
              (.retain (130164399590400000 / 125067512150729))
            )
            (.retain (149652424074240000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (144417805885440000 / 125067512150729))
              (.retain (159752457584640000 / 125067512150729))
            )
            (.retain (154037839380480000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (158183343959040000 / 125067512150729))
              (.retain (173627180006400000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (197010899573760000 / 125067512150729))
              (.retain (194678903024640000 / 125067512150729))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (143883028224000000 / 125067512150729))
              (.retain (158018860661760000 / 125067512150729))
            )
            (.retain (152920076958720000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (156380840340480000 / 125067512150729))
              (.retain (170461424563200000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (190387703531520000 / 125067512150729))
              (.retain (189656627788800000 / 125067512150729))
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
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5) root = (153334199971 / 100000000000000) := by
  decide +kernel

end C051S009
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
