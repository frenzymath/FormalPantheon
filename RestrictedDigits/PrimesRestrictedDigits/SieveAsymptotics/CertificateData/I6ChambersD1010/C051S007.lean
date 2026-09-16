import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C051S007
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C051S007

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(82507 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
    ![(24689 / 187500), (244997 / 3000000), (244997 / 3000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (1 / 2)
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 0 (1 / 2)
          (.retain (15110310170880000 / 125067512150729))
          (.split 2 (1 / 2)
            (.retain (29527220897280000 / 125067512150729))
            (.retain (58446153584640000 / 125067512150729))
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (346729628160000 / 2908546794203))
            (.retain (44077088424960000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (15210726059520000 / 125067512150729))
            (.retain (44378361976320000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (59315823866880000 / 125067512150729))
            (.split 1 (1 / 2)
              (.retain (87545613404160000 / 125067512150729))
              (.retain (88504944629760000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.retain (45030916823040000 / 125067512150729))
            (.retain (45675329287680000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (87549440486400000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (115085948497920000 / 125067512150729))
              (.retain (116285112576000000 / 125067512150729))
            )
          )
          (.split 5 (1 / 2)
            (.retain (109582442956800000 / 125067512150729))
            (.retain (151828956771840000 / 125067512150729))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 4 (1 / 2)
        (.split 1 (1 / 2)
          (.retain (15773551061760000 / 125067512150729))
          (.split 2 (1 / 2)
            (.retain (31202154593280000 / 125067512150729))
            (.retain (63525257717760000 / 125067512150729))
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (16199172149760000 / 125067512150729))
            (.retain (48736742031360000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (17317423065600000 / 125067512150729))
            (.retain (49858090790400000 / 125067512150729))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (45682431575040000 / 125067512150729))
            (.retain (46326844039680000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.retain (60982434961920000 / 125067512150729))
            (.split 0 (1 / 2)
              (.retain (93971998402560000 / 125067512150729))
              (.retain (92181251036160000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (90312058483200000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (121416211906560000 / 125067512150729))
              (.retain (123654646149120000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.retain (110359497899520000 / 125067512150729))
            (.retain (155219299937280000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 5) (i6D1006LeafValid 2 0 5) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5) root = (41717530993 / 50000000000000) := by
  decide +kernel

end C051S007
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
