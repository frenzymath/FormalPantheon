import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S022
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S022

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 2000000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(309993 / 4000000), (309993 / 4000000), (309993 / 4000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (251691529390080000 / 125067512150729))
            (.retain (164015823697920000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (107308742830080000 / 125067512150729))
            (.retain (111025602754560000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.retain (51962775290880000 / 125067512150729))
          (.retain (55421474903040000 / 125067512150729))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (261729230039040000 / 125067512150729))
            (.retain (170707624120320000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (112327593154560000 / 125067512150729))
            (.retain (116044453079040000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.retain (33063859200000 / 67640623121))
          (.retain (60777598955520000 / 125067512150729))
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (272576586670080000 / 125067512150729))
            (.retain (177939195217920000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (125812874403840000 / 125067512150729))
            (.retain (130959641118720000 / 125067512150729))
          )
        )
        (.split 3 (1 / 2)
          (.retain (65209412290560000 / 125067512150729))
          (.retain (65566888995840000 / 125067512150729))
        )
      )
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (299325014999040000 / 125067512150729))
              (.retain (266863230013440000 / 125067512150729))
            )
            (.retain (185805254430720000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (131712418805760000 / 125067512150729))
            (.retain (136859185551360000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.retain (71505414282240000 / 125067512150729))
          (.retain (77147181972480000 / 125067512150729))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (15287522471 / 12500000000000) := by
  decide +kernel

end C046S022
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
