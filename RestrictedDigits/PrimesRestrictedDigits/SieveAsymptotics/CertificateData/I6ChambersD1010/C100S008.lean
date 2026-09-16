import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S008
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S008

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(398470879 / 1651600000), (55499 / 600000), (55499 / 600000)],
    ![(101501 / 400000), (212499 / 2000000), (342491 / 4000000)],
    ![(212499 / 1000000), (147503 / 1000000), (212499 / 2000000)],
    ![(43 / 200), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (340381137 / 650072653));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (340381137 / 650072653));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (196073399630177280000 / 772370756866053571))
              (.retain (99466208449597440000 / 772370756866053571))
            )
            (.retain (48561394135541760000 / 772370756866053571))
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (205115106778168320000 / 772370756866053571))
              (.retain (104906384018933760000 / 772370756866053571))
            )
            (.retain (56103833377681920000 / 772370756866053571))
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (260272293064796160000 / 772370756866053571))
              (.retain (160354010312156160000 / 772370756866053571))
            )
            (.retain (115180126746877440000 / 772370756866053571))
          )
          (.retain (60561758549952000000 / 772370756866053571))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (295180133328368640000 / 772370756866053571))
              (.retain (201256972370380800000 / 772370756866053571))
            )
            (.retain (211086073280678400000 / 772370756866053571))
          )
          (.retain (124837448467184640000 / 772370756866053571))
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (71252712403130880000 / 772370756866053571))
            (.retain (78195987611458560000 / 772370756866053571))
          )
          (.retain (70864741383989760000 / 772370756866053571))
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (326065217357352960000 / 772370756866053571))
              (.retain (296150571545656320000 / 772370756866053571))
            )
            (.retain (214212631198924800000 / 772370756866053571))
          )
          (.split 1 (1 / 2)
            (.retain (190665892444584960000 / 772370756866053571))
            (.retain (257055633289774080000 / 772370756866053571))
          )
        )
        (.split 1 (1 / 2)
          (.retain (144075209092750080000 / 772370756866053571))
          (.split 0 (1 / 2)
            (.retain (187823195668408320000 / 772370756866053571))
            (.retain (133244840057978880000 / 772370756866053571))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.retain (78017921469976320000 / 772370756866053571))
          (.split 2 (1 / 2)
            (.retain (119379293680665600000 / 772370756866053571))
            (.retain (57313611837480960000 / 772370756866053571))
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (153953828242536960000 / 772370756866053571))
            (.retain (93524716839352320000 / 772370756866053571))
          )
          (.retain (51714442412363520000 / 772370756866053571))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (8661880403 / 20000000000000) := by
  decide +kernel

end C100S008
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
