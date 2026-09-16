import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S009
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S009

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(410011 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(23001 / 200000), (180001 / 2000000), (16249 / 250000)],
    ![(180001 / 2000000), (180001 / 2000000), (180001 / 2000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 5 (1 / 2)
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (376542847610880000 / 125067512150729))
              (.retain (363122244341760000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (315045415219200000 / 125067512150729))
              (.retain (342301568409600000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (310925040353280000 / 125067512150729))
              (.retain (327521676656640000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (315757449953280000 / 125067512150729))
              (.retain (343064462745600000 / 125067512150729))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (318078292070400000 / 125067512150729))
              (.retain (289213078179840000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (284917603000320000 / 125067512150729))
              (.retain (304107682344960000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (324174928896000000 / 125067512150729))
              (.retain (306206277980160000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (309843517870080000 / 125067512150729))
              (.retain (301577755422720000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (182271384975360000 / 125067512150729))
            (.retain (122519996989440000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (253720944138240000 / 125067512150729))
            (.retain (210389885184000000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (5324840755200000 / 2908546794203))
            (.retain (271824572559360000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (237862919024640000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (287068557250560000 / 125067512150729))
              (.retain (276433894379520000 / 125067512150729))
            )
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (252435724984320000 / 125067512150729))
            (.retain (4736561203200000 / 2908546794203))
          )
          (.split 1 (1 / 2)
            (.retain (119612508825600000 / 125067512150729))
            (.retain (179683270594560000 / 125067512150729))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (272614857768960000 / 125067512150729))
            (.retain (226784441395200000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (222268575559680000 / 125067512150729))
            (.retain (228175269765120000 / 125067512150729))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (255977171159040000 / 125067512150729))
            (.retain (212216354672640000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (123018911600640000 / 125067512150729))
            (.retain (184603630141440000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (275531286896640000 / 125067512150729))
            (.retain (232000918732800000 / 125067512150729))
          )
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (288472652820480000 / 125067512150729))
              (.retain (277715894661120000 / 125067512150729))
            )
            (.retain (238961776404480000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (256059899273 / 100000000000000) := by
  decide +kernel

end C046S009
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
