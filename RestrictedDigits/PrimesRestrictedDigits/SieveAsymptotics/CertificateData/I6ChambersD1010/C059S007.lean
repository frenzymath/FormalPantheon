import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S007
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S007

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)],
    ![(38701 / 240000), (180001 / 1500000), (472483 / 6000000)],
    ![(147503 / 1000000), (212499 / 2000000), (212499 / 2000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1007085995458560000 / 561658568377843))
              (.retain (942870037340160000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (895872845905920000 / 561658568377843))
              (.retain (868298189783040000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (830050688655360000 / 561658568377843))
              (.retain (799092051886080000 / 561658568377843))
            )
            (.retain (720322618613760000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (676278019399680000 / 561658568377843))
            (.split 4 (1 / 2)
              (.retain (743562921000960000 / 561658568377843))
              (.retain (704730717757440000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (752660558438400000 / 561658568377843))
              (.retain (716066870722560000 / 561658568377843))
            )
            (.retain (632121073090560000 / 561658568377843))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (1026242058977280000 / 561658568377843))
              (.retain (1002490749665280000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (890110834606080000 / 561658568377843))
              (.retain (958105213009920000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (844614636503040000 / 561658568377843))
              (.retain (916081957969920000 / 561658568377843))
            )
            (.retain (744273739468800000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (906490005995520000 / 561658568377843))
              (.retain (827929875824640000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (929998284595200000 / 561658568377843))
              (.retain (901485618462720000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (889367392051200000 / 561658568377843))
              (.retain (812609642004480000 / 561658568377843))
            )
            (.retain (708073629143040000 / 561658568377843))
          )
        )
      )
    )
    (.split 2 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (990514148474880000 / 561658568377843))
              (.retain (927679177728000000 / 561658568377843))
            )
            (.retain (837627949117440000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (786411082137600000 / 561658568377843))
            (.retain (694538444206080000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (663744307875840000 / 561658568377843))
            (.retain (647651085189120000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.retain (726405571031040000 / 561658568377843))
            (.retain (629187354132480000 / 561658568377843))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (527944882176000000 / 561658568377843))
            (.retain (494415329955840000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.retain (522030519152640000 / 561658568377843))
            (.retain (476807786864640000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (487073675612160000 / 561658568377843))
            (.retain (453078121512960000 / 561658568377843))
          )
          (.retain (299466564986880000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (61222123359 / 50000000000000) := by
  decide +kernel

end C059S007
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
