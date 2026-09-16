import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S027
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S027

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (1 / 2)
    (.split 2 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (1162198300262400000 / 561658568377843))
                (.retain (1103371117977600000 / 561658568377843))
              )
              (.split 0 (1 / 2)
                (.retain (1064187342766080000 / 561658568377843))
                (.retain (1062293630976000000 / 561658568377843))
              )
            )
            (.split 0 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (990245284945920000 / 561658568377843))
                (.retain (992016821698560000 / 561658568377843))
              )
              (.retain (917462877696000000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (913605154652160000 / 561658568377843))
              (.retain (967266370252800000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (874072331550720000 / 561658568377843))
              (.retain (852693990543360000 / 561658568377843))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (859427302625280000 / 561658568377843))
              (.retain (799457582960640000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (852106185031680000 / 561658568377843))
              (.retain (778646836961280000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (856484576686080000 / 561658568377843))
              (.retain (796770746265600000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (846156861665280000 / 561658568377843))
              (.retain (767784319303680000 / 561658568377843))
            )
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (689589990051840000 / 561658568377843))
              (.retain (707250358702080000 / 561658568377843))
            )
            (.retain (618991900139520000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (712034370478080000 / 561658568377843))
              (.retain (699277479690240000 / 561658568377843))
            )
            (.retain (621083512719360000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (615625190830080000 / 561658568377843))
              (.retain (631426573393920000 / 561658568377843))
            )
            (.retain (540009498562560000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (525201474908160000 / 561658568377843))
              (.retain (439673778339840000 / 561658568377843))
            )
            (.retain (302894624839680000 / 561658568377843))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (538325012090880000 / 561658568377843))
              (.retain (442953580769280000 / 561658568377843))
            )
            (.retain (295840475596800000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (524688585523200000 / 561658568377843))
              (.retain (431589892055040000 / 561658568377843))
            )
            (.split 5 (1 / 2)
              (.retain (533597629501440000 / 561658568377843))
              (.retain (395109384007680000 / 561658568377843))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (688118851399680000 / 561658568377843))
              (.retain (605095343308800000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (599472492871680000 / 561658568377843))
              (.retain (669660811960320000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (601975729336320000 / 561658568377843))
              (.retain (515085753507840000 / 561658568377843))
            )
            (.retain (543598995363840000 / 561658568377843))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (489063557836800000 / 561658568377843))
              (.retain (285393813073920000 / 561658568377843))
            )
            (.retain (181230941583360000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (539192139816960000 / 561658568377843))
              (.retain (399361211781120000 / 561658568377843))
            )
            (.retain (273540571822080000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (508930115788800000 / 561658568377843))
            (.retain (319189061007360000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (262019916011520000 / 561658568377843))
            (.retain (160656453918720000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (199673538007 / 100000000000000) := by
  decide +kernel

end C059S027
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
