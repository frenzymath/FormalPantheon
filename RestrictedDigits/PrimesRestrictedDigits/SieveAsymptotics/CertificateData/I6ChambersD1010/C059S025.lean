import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S025
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S025

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(147503 / 1000000), (147503 / 1000000), (16249 / 250000)],
    ![(802511 / 6000000), (802511 / 6000000), (55499 / 600000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (657291152424960000 / 561658568377843))
              (.retain (569398637445120000 / 561658568377843))
            )
            (.retain (389398331197440000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (279621816422400000 / 561658568377843))
            (.retain (271207186698240000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (153645774658560000 / 561658568377843))
          (.retain (144274751539200000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (647572692234240000 / 561658568377843))
              (.retain (543705706045440000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (434277611642880000 / 561658568377843))
              (.retain (318066904166400000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.retain (329075827845120000 / 561658568377843))
            (.retain (202666952908800000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (134699255516160000 / 561658568377843))
          (.retain (134072186250240000 / 561658568377843))
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (628701453803520000 / 561658568377843))
              (.retain (527737735065600000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (307905468088320000 / 561658568377843))
              (.retain (421212908113920000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.retain (245936260270080000 / 561658568377843))
            (.retain (239999879669760000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (126896681088000000 / 561658568377843))
          (.retain (127523750353920000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (461276228597760000 / 561658568377843))
            (.retain (242522948413440000 / 561658568377843))
          )
          (.split 5 (1 / 2)
            (.retain (444767182479360000 / 561658568377843))
            (.retain (227357669283840000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (120696162462720000 / 561658568377843))
          (.retain (115152757032960000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (86541754081 / 100000000000000) := by
  decide +kernel

end C059S025
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
