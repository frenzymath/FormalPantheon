import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S031
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S031

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1097517 / 8000000), (767489 / 8000000), (767489 / 8000000)],
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)],
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (1 / 2)
    (.split 5 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (1111277843066880000 / 561658568377843))
              (.split 3 (1 / 2)
                (.retain (1040940138700800000 / 561658568377843))
                (.retain (1042833850490880000 / 561658568377843))
              )
            )
            (.split 3 (1 / 2)
              (.retain (898864674693120000 / 561658568377843))
              (.split 4 (1 / 2)
                (.retain (970269437214720000 / 561658568377843))
                (.retain (972040973967360000 / 561658568377843))
              )
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (817817710325760000 / 561658568377843))
              (.retain (891887895429120000 / 561658568377843))
            )
            (.retain (841027299010560000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (828501139722240000 / 561658568377843))
              (.retain (751663877529600000 / 561658568377843))
            )
            (.retain (777412395325440000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (834449792163840000 / 561658568377843))
              (.retain (762525782691840000 / 561658568377843))
            )
            (.retain (780226535024640000 / 561658568377843))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (513630980444160000 / 561658568377843))
              (.retain (429883359805440000 / 561658568377843))
            )
            (.retain (295774320568320000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (589224738816000000 / 561658568377843))
              (.retain (509320923217920000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (504588657623040000 / 561658568377843))
              (.retain (573329508802560000 / 561658568377843))
            )
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (675004828446720000 / 561658568377843))
              (.retain (597324741672960000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (591916438425600000 / 561658568377843))
              (.retain (657199804354560000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (601590916730880000 / 561658568377843))
              (.retain (684691763834880000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (594091000811520000 / 561658568377843))
              (.retain (659630197739520000 / 561658568377843))
            )
          )
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (490247372574720000 / 561658568377843))
              (.retain (417874833285120000 / 561658568377843))
            )
            (.retain (284702865684480000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.retain (199190411642880000 / 561658568377843))
            (.retain (195665101885440000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (543793864826880000 / 561658568377843))
              (.retain (471668833198080000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (585019126886400000 / 561658568377843))
              (.retain (599893375979520000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (491993827061760000 / 561658568377843))
              (.retain (419352602296320000 / 561658568377843))
            )
            (.retain (285777606850560000 / 561658568377843))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (444289465497600000 / 561658568377843))
            (.retain (277514481438720000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (564802658242560000 / 561658568377843))
              (.retain (492871202795520000 / 561658568377843))
            )
            (.retain (543591819048960000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (187472458414080000 / 561658568377843))
            (.retain (185369035438080000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (459009467688960000 / 561658568377843))
            (.retain (276006427453440000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (92868478341 / 50000000000000) := by
  decide +kernel

end C059S031
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
