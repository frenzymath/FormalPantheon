import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S013
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S013

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(672519 / 4000000), (342491 / 4000000), (342491 / 4000000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (607615235297280000 / 561658568377843))
              (.retain (529246057144320000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (496145995223040000 / 561658568377843))
              (.retain (514472395898880000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (395239014604800000 / 561658568377843))
              (.retain (410233342464000000 / 561658568377843))
            )
            (.retain (297420612433920000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (189113876029440000 / 561658568377843))
            (.retain (311149491333120000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.retain (302625460869120000 / 561658568377843))
            (.retain (188238982164480000 / 561658568377843))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (654332545843200000 / 561658568377843))
              (.retain (674951842160640000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (567558555033600000 / 561658568377843))
              (.retain (648160163389440000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (519154701557760000 / 561658568377843))
              (.retain (603391600926720000 / 561658568377843))
            )
            (.retain (353890135111680000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (695263932518400000 / 561658568377843))
              (.retain (608168164147200000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (749376211230720000 / 561658568377843))
              (.retain (777429382164480000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (624223197941760000 / 561658568377843))
              (.retain (536781437521920000 / 561658568377843))
            )
            (.retain (366709579407360000 / 561658568377843))
          )
        )
      )
    )
    (.split 2 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (639431107891200000 / 561658568377843))
              (.retain (660050404208640000 / 561658568377843))
            )
            (.retain (566577497733120000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (335397810769920000 / 561658568377843))
            (.retain (535212522547200000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (619768713830400000 / 561658568377843))
              (.retain (412786533888000000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (730119118417920000 / 561658568377843))
              (.retain (758172289351680000 / 561658568377843))
            )
          )
          (.split 5 (1 / 2)
            (.retain (595410377011200000 / 561658568377843))
            (.split 1 (1 / 2)
              (.retain (347123967528960000 / 561658568377843))
              (.retain (442491592089600000 / 561658568377843))
            )
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (288273636864000000 / 561658568377843))
            (.retain (181837880064000000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.retain (286703201986560000 / 561658568377843))
            (.retain (178882383513600000 / 561658568377843))
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (438555104686080000 / 561658568377843))
              (.retain (457292286812160000 / 561658568377843))
            )
            (.retain (348374782402560000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (651733339484160000 / 561658568377843))
            (.retain (413326077880320000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (156788683751 / 100000000000000) := by
  decide +kernel

end C059S013
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
