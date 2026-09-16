import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S010
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S010

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)],
    ![(147503 / 1000000), (212499 / 2000000), (212499 / 2000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (1 / 2)
    (.split 2 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (1193382809395200000 / 561658568377843))
              (.retain (1171561314263040000 / 561658568377843))
            )
            (.retain (1113178422067200000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (949179157954560000 / 561658568377843))
              (.retain (1003132182896640000 / 561658568377843))
            )
            (.retain (1077682356264960000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1070147516497920000 / 561658568377843))
              (.retain (965521529487360000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (1110541307535360000 / 561658568377843))
              (.retain (1089712260218880000 / 561658568377843))
            )
          )
          (.split 5 (1 / 2)
            (.retain (1081448251637760000 / 561658568377843))
            (.split 1 (1 / 2)
              (.retain (952451165306880000 / 561658568377843))
              (.retain (1006651134074880000 / 561658568377843))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (919773004861440000 / 561658568377843))
            (.retain (860002840535040000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (991794832220160000 / 561658568377843))
              (.retain (927230942453760000 / 561658568377843))
            )
            (.retain (986856501104640000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (969719365877760000 / 561658568377843))
              (.retain (906790695690240000 / 561658568377843))
            )
            (.retain (965598644551680000 / 561658568377843))
          )
          (.retain (880785653944320000 / 561658568377843))
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (641968319692800000 / 561658568377843))
            (.retain (549594482503680000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (331120707010560000 / 561658568377843))
            (.retain (486687203389440000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (699159895879680000 / 561658568377843))
            (.retain (611315828858880000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (723064966225920000 / 561658568377843))
              (.retain (639422848696320000 / 561658568377843))
            )
            (.retain (670478930104320000 / 561658568377843))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (786589086044160000 / 561658568377843))
            (.retain (756537819770880000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.retain (845533836840960000 / 561658568377843))
            (.retain (934034037534720000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (807453218672640000 / 561658568377843))
            (.retain (894894649528320000 / 561658568377843))
          )
          (.retain (837750356674560000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (1156791351 / 781250000000) := by
  decide +kernel

end C059S010
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
