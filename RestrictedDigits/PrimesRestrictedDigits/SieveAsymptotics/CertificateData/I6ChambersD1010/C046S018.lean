import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S018
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S018

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(180001 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(23001 / 200000), (16249 / 250000), (16249 / 250000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 5 (1 / 2)
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (375798840299520000 / 125067512150729))
                (.retain (361198043873280000 / 125067512150729))
              )
              (.split 0 (1 / 2)
                (.retain (345051662499840000 / 125067512150729))
                (.retain (327200715018240000 / 125067512150729))
              )
            )
            (.split 1 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (287894286336000000 / 125067512150729))
                (.retain (316649245224960000 / 125067512150729))
              )
              (.split 0 (1 / 2)
                (.retain (321927403622400000 / 125067512150729))
                (.retain (302553145651200000 / 125067512150729))
              )
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (303965324206080000 / 125067512150729))
                (.retain (273603687997440000 / 125067512150729))
              )
              (.split 4 (1 / 2)
                (.retain (309592989020160000 / 125067512150729))
                (.retain (289139608350720000 / 125067512150729))
              )
            )
            (.split 1 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (303282277601280000 / 125067512150729))
                (.retain (272980036730880000 / 125067512150729))
              )
              (.split 2 (1 / 2)
                (.retain (308154423828480000 / 125067512150729))
                (.retain (286381865349120000 / 125067512150729))
              )
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (250975702579200000 / 125067512150729))
              (.retain (243316535777280000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (243851093975040000 / 125067512150729))
              (.retain (252745860526080000 / 125067512150729))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (220113357189120000 / 125067512150729))
              (.retain (213305208913920000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (194460489646080000 / 125067512150729))
              (.retain (126838657996800000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (171415810805760000 / 125067512150729))
              (.retain (111817258014720000 / 125067512150729))
            )
            (.retain (75466006318080000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (207596899983360000 / 125067512150729))
              (.retain (215503359129600000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (177161816494080000 / 125067512150729))
              (.retain (115647928442880000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (182883585853440000 / 125067512150729))
              (.retain (119462441349120000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (214272297584640000 / 125067512150729))
              (.retain (222178756730880000 / 125067512150729))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (182461935144960000 / 125067512150729))
              (.retain (119181340876800000 / 125067512150729))
            )
            (.retain (85302553912320000 / 125067512150729))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (191962774425600000 / 125067512150729))
              (.retain (125118387363840000 / 125067512150729))
            )
            (.retain (84087234247680000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (40283521474560000 / 125067512150729))
            (.retain (42635448913920000 / 125067512150729))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (199692624537600000 / 125067512150729))
              (.retain (130271620792320000 / 125067512150729))
            )
            (.retain (87952159319040000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (47394634398720000 / 125067512150729))
            (.retain (46760102323200000 / 125067512150729))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (191096013772800000 / 125067512150729))
              (.retain (124540546928640000 / 125067512150729))
            )
            (.retain (83042864040960000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (39978026526720000 / 125067512150729))
            (.retain (42329953966080000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (196817783132160000 / 125067512150729))
              (.retain (128355059834880000 / 125067512150729))
            )
            (.retain (85903748720640000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (45383094082560000 / 125067512150729))
            (.retain (45187909355520000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (30173002737 / 10000000000000) := by
  decide +kernel

end C046S018
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
