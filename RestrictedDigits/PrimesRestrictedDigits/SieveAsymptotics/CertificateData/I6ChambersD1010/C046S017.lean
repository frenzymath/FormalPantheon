import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S017
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S017

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(180001 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(23001 / 200000), (180001 / 2000000), (16249 / 250000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (1 / 2)
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (369455162757120000 / 125067512150729))
                (.retain (343140510412800000 / 125067512150729))
              )
              (.split 1 (1 / 2)
                (.retain (327678733516800000 / 125067512150729))
                (.retain (321568258129920000 / 125067512150729))
              )
            )
            (.split 0 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (300843688058880000 / 125067512150729))
                (.retain (283022140108800000 / 125067512150729))
              )
              (.split 1 (1 / 2)
                (.retain (305767547904000000 / 125067512150729))
                (.retain (297353954672640000 / 125067512150729))
              )
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (251971215974400000 / 125067512150729))
              (.retain (260190634752000000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (268943869071360000 / 125067512150729))
              (.retain (278305072957440000 / 125067512150729))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (234159596236800000 / 125067512150729))
              (.retain (226500429434880000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (212613713264640000 / 125067512150729))
              (.retain (219338692270080000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (212570883440640000 / 125067512150729))
              (.retain (205762735165440000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (187995512156160000 / 125067512150729))
              (.retain (122528673024000000 / 125067512150729))
            )
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (186997854566400000 / 125067512150729))
              (.retain (181020095447040000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (165369335930880000 / 125067512150729))
              (.retain (107786274754560000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (165694041446400000 / 125067512150729))
              (.retain (108002745108480000 / 125067512150729))
            )
            (.retain (72605121638400000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (192806175989760000 / 125067512150729))
              (.retain (186828416870400000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (170347897159680000 / 125067512150729))
              (.retain (111105315563520000 / 125067512150729))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (175996957624320000 / 125067512150729))
              (.retain (114871355873280000 / 125067512150729))
            )
            (.retain (82070065152000000 / 125067512150729))
          )
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (145753069793280000 / 125067512150729))
              (.retain (95008803747840000 / 125067512150729))
            )
            (.retain (63883839191040000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (30992212285440000 / 125067512150729))
            (.retain (32564547594240000 / 125067512150729))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (150159299973120000 / 125067512150729))
              (.retain (97946290544640000 / 125067512150729))
            )
            (.retain (66086954280960000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (35031201377280000 / 125067512150729))
            (.retain (34915715097600000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (154834243891200000 / 125067512150729))
              (.retain (101062919823360000 / 125067512150729))
            )
            (.retain (72211796305920000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (36809400130560000 / 125067512150729))
            (.retain (36924886410240000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (159812805120000000 / 125067512150729))
              (.retain (104381960632320000 / 125067512150729))
            )
            (.retain (74701076920320000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (39465963863040000 / 125067512150729))
            (.retain (41738192855040000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (269241010143 / 100000000000000) := by
  decide +kernel

end C046S017
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
