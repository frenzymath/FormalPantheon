import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S004
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S004

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(38701 / 240000), (180001 / 1500000), (472483 / 6000000)],
    ![(147503 / 1000000), (147503 / 1000000), (16249 / 250000)],
    ![(802511 / 6000000), (802511 / 6000000), (55499 / 600000)]
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (657357199810560000 / 561658568377843))
            (.retain (514040030208000000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.retain (423783564226560000 / 561658568377843))
            (.retain (290877203681280000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (236471266713600000 / 561658568377843))
          (.retain (228725704304640000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (720219633868800000 / 561658568377843))
              (.retain (678809828597760000 / 561658568377843))
            )
            (.retain (566103806484480000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (506787151011840000 / 561658568377843))
            (.retain (322301021184000000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (462425052303360000 / 561658568377843))
            (.retain (518962132869120000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.retain (453770869985280000 / 561658568377843))
            (.retain (260152944168960000 / 561658568377843))
          )
        )
      )
    )
    (.split 2 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (728659364659200000 / 561658568377843))
              (.retain (689308055470080000 / 561658568377843))
            )
            (.retain (606674427125760000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (368699561717760000 / 561658568377843))
            (.retain (538868136960000000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (410567264501760000 / 561658568377843))
            (.retain (536108158586880000 / 561658568377843))
          )
          (.split 5 (1 / 2)
            (.retain (540388937134080000 / 561658568377843))
            (.retain (369785847398400000 / 561658568377843))
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.retain (210323794083840000 / 561658568377843))
          (.split 4 (1 / 2)
            (.retain (337010016337920000 / 561658568377843))
            (.retain (350163321200640000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.retain (333180466513920000 / 561658568377843))
          (.retain (207057537146880000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (17462622919 / 25000000000000) := by
  decide +kernel

end C059S004
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
