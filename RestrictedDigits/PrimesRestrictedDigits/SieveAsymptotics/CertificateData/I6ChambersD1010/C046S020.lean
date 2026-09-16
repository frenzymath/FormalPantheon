import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S020
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S020

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(180001 / 2000000), (16249 / 250000), (16249 / 250000)],
    ![(23001 / 200000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 2000000), (180001 / 2000000), (16249 / 250000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 2 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (389559346176000000 / 125067512150729))
                (.retain (374124579655680000 / 125067512150729))
              )
              (.split 3 (1 / 2)
                (.retain (338459310735360000 / 125067512150729))
                (.retain (357144228188160000 / 125067512150729))
              )
            )
            (.split 1 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (324178019635200000 / 125067512150729))
                (.retain (345360182292480000 / 125067512150729))
              )
              (.split 0 (1 / 2)
                (.retain (351866058424320000 / 125067512150729))
                (.retain (343127800688640000 / 125067512150729))
              )
            )
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (319354672189440000 / 125067512150729))
                (.retain (296608179118080000 / 125067512150729))
              )
              (.split 2 (1 / 2)
                (.retain (325360096296960000 / 125067512150729))
                (.retain (313931911864320000 / 125067512150729))
              )
            )
            (.split 0 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (321013619589120000 / 125067512150729))
                (.retain (299567140638720000 / 125067512150729))
              )
              (.split 2 (1 / 2)
                (.retain (326263525109760000 / 125067512150729))
                (.retain (314756781649920000 / 125067512150729))
              )
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (201374502236160000 / 125067512150729))
              (.retain (131447999723520000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (235971182315520000 / 125067512150729))
              (.retain (244975952363520000 / 125067512150729))
            )
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (259741114337280000 / 125067512150729))
              (.retain (269871480637440000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (261683745331200000 / 125067512150729))
              (.retain (270578511882240000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (217244342292480000 / 125067512150729))
              (.retain (141575919575040000 / 125067512150729))
            )
            (.retain (94379899929600000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (246255068313600000 / 125067512150729))
              (.retain (238348609167360000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (217802036920320000 / 125067512150729))
              (.retain (141947715993600000 / 125067512150729))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (226535927439360000 / 125067512150729))
              (.retain (147770309652480000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (256444607262720000 / 125067512150729))
              (.retain (248538148116480000 / 125067512150729))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (235318749327360000 / 125067512150729))
              (.retain (153625524264960000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (108639128832000000 / 125067512150729))
              (.retain (113070942167040000 / 125067512150729))
            )
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (203867839641600000 / 125067512150729))
              (.retain (133055097507840000 / 125067512150729))
            )
            (.retain (95049116697600000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (47998079216640000 / 125067512150729))
            (.retain (48193263943680000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (212601730160640000 / 125067512150729))
              (.retain (138877691197440000 / 125067512150729))
            )
            (.retain (99416061957120000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (52853674014720000 / 125067512150729))
            (.retain (56474665605120000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (207027118571520000 / 125067512150729))
              (.retain (135161283471360000 / 125067512150729))
            )
            (.retain (2272322135040000 / 2908546794203))
          )
          (.split 3 (1 / 2)
            (.retain (49805325066240000 / 125067512150729))
            (.retain (50439857141760000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (213752928307200000 / 125067512150729))
              (.retain (139645156638720000 / 125067512150729))
            )
            (.retain (101072756674560000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (53394221829120000 / 125067512150729))
            (.retain (57015213419520000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (42442594663 / 12500000000000) := by
  decide +kernel

end C046S020
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
