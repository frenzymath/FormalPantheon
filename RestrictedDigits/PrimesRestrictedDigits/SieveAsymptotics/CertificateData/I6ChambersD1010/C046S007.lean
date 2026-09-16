import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S007
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S007

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(23001 / 200000), (180001 / 2000000), (16249 / 250000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
    ![(410011 / 4000000), (410011 / 4000000), (309993 / 4000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (1 / 2)
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (154718783109120000 / 125067512150729))
            (.retain (103888764088320000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (102421531299840000 / 125067512150729))
            (.retain (102762263316480000 / 125067512150729))
          )
        )
        (.split 3 (1 / 2)
          (.retain (45195176110080000 / 125067512150729))
          (.split 4 (1 / 2)
            (.retain (74268062146560000 / 125067512150729))
            (.retain (74533075937280000 / 125067512150729))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (159492199157760000 / 125067512150729))
            (.retain (107193436753920000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (104420076902400000 / 125067512150729))
            (.retain (107384017551360000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.retain (64502366592000000 / 125067512150729))
          (.retain (66396051624960000 / 125067512150729))
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (183680908277760000 / 125067512150729))
            (.retain (184371368724480000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (156095464734720000 / 125067512150729))
            (.retain (160376712314880000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (151558682726400000 / 125067512150729))
            (.retain (147606761871360000 / 125067512150729))
          )
          (.retain (97600890485760000 / 125067512150729))
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (157775622389760000 / 125067512150729))
            (.retain (163335093903360000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.retain (188536429086720000 / 125067512150729))
            (.retain (190738870272000000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (148125895925760000 / 125067512150729))
            (.retain (3564132925440000 / 2908546794203))
          )
          (.retain (98387489832960000 / 125067512150729))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (124371929869 / 100000000000000) := by
  decide +kernel

end C046S007
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
