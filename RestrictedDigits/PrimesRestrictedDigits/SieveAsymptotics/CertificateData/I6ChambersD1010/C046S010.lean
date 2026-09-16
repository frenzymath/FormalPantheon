import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S010
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S010

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(23001 / 200000), (16249 / 250000), (16249 / 250000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(23001 / 200000), (180001 / 2000000), (16249 / 250000)],
    ![(410011 / 4000000), (309993 / 4000000), (309993 / 4000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 4 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (217491342028800000 / 125067512150729))
            (.retain (211303912980480000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (181058163978240000 / 125067512150729))
            (.retain (118159210721280000 / 125067512150729))
          )
        )
        (.split 3 (1 / 2)
          (.retain (76409605939200000 / 125067512150729))
          (.split 0 (1 / 2)
            (.retain (175110617149440000 / 125067512150729))
            (.retain (114194179491840000 / 125067512150729))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (170568746803200000 / 125067512150729))
            (.retain (2585261998080000 / 2908546794203))
          )
          (.retain (74138670766080000 / 125067512150729))
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (194747670128640000 / 125067512150729))
            (.retain (189773611868160000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.retain (171608069191680000 / 125067512150729))
            (.retain (111859147530240000 / 125067512150729))
          )
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (226509500528640000 / 125067512150729))
            (.retain (220322071480320000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (123312444149760000 / 125067512150729))
            (.retain (188788014120960000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (124220541081600000 / 125067512150729))
            (.retain (190150159534080000 / 125067512150729))
          )
          (.retain (89902296176640000 / 125067512150729))
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (178540924385280000 / 125067512150729))
            (.retain (116481051002880000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.retain (202836001198080000 / 125067512150729))
            (.retain (197861942906880000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (184811294208000000 / 125067512150729))
            (.retain (120661297551360000 / 125067512150729))
          )
          (.retain (87232863513600000 / 125067512150729))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (152893979581 / 100000000000000) := by
  decide +kernel

end C046S010
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
