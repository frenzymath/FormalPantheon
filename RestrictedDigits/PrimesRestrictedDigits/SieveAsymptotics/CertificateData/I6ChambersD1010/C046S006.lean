import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S006

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(23001 / 200000), (180001 / 2000000), (16249 / 250000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(410011 / 4000000), (410011 / 4000000), (309993 / 4000000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 2 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (370012591349760000 / 125067512150729))
              (.retain (344488228454400000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (324717281955840000 / 125067512150729))
              (.retain (309564250767360000 / 125067512150729))
            )
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (319606848061440000 / 125067512150729))
              (.retain (304794512424960000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (321648348426240000 / 125067512150729))
              (.retain (305443267399680000 / 125067512150729))
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (256735584460800000 / 125067512150729))
            (.retain (265328613181440000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (294415015403520000 / 125067512150729))
              (.retain (278600948244480000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (296318813859840000 / 125067512150729))
              (.retain (279201647247360000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (220004386406400000 / 125067512150729))
            (.retain (212905797457920000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (266975189452800000 / 125067512150729))
            (.retain (220438909562880000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (199574292602880000 / 125067512150729))
            (.retain (249195591290880000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.retain (176072801495040000 / 125067512150729))
            (.retain (118228669962240000 / 125067512150729))
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (259316313108480000 / 125067512150729))
            (.retain (214112011683840000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (209777776435200000 / 125067512150729))
            (.retain (210549467535360000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (242202704179200000 / 125067512150729))
            (.retain (193913383987200000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (3922421913600000 / 2908546794203))
            (.retain (116557619312640000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (262484875622400000 / 125067512150729))
            (.retain (218416195276800000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (215542398812160000 / 125067512150729))
            (.retain (218003950725120000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (243186610851840000 / 125067512150729))
            (.retain (196184753633280000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (169942366218240000 / 125067512150729))
            (.retain (117442543564800000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (238156341989 / 100000000000000) := by
  decide +kernel

end C046S006
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
