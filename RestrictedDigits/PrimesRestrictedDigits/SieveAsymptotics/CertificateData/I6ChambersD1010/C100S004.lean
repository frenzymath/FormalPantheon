import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S004
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S004

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(43 / 200), (180001 / 1500000), (180001 / 1500000)],
    ![(101501 / 400000), (212499 / 2000000), (342491 / 4000000)],
    ![(212499 / 1000000), (147503 / 1000000), (212499 / 2000000)],
    ![(126251 / 500000), (43 / 400), (43 / 400)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (63756 / 82507));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (63756 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (1 / 2)
    (.split 5 (1 / 2)
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (2281552291680000 / 2739894188647))
              (.retain (2026280312160000 / 2739894188647))
            )
            (.split 3 (1 / 2)
              (.retain (1612859968800000 / 2739894188647))
              (.retain (1691578138560000 / 2739894188647))
            )
          )
          (.split 0 (1 / 2)
            (.retain (892565944320000 / 2739894188647))
            (.split 5 (1 / 2)
              (.retain (1451570624640000 / 2739894188647))
              (.retain (1381059944640000 / 2739894188647))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (195548210400000 / 391413455521))
              (.retain (1133922449280000 / 2739894188647))
            )
            (.retain (751071588240000 / 2739894188647))
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1419319943040000 / 2739894188647))
              (.retain (1188910978560000 / 2739894188647))
            )
            (.split 2 (1 / 2)
              (.retain (1450729500960000 / 2739894188647))
              (.retain (75777147840000 / 161170246391))
            )
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (563145035280000 / 2739894188647))
            (.retain (287051660640000 / 2739894188647))
          )
          (.split 0 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (671070608640000 / 2739894188647))
              (.retain (80059382400000 / 391413455521))
            )
            (.split 2 (1 / 2)
              (.retain (929067101280000 / 2739894188647))
              (.retain (43296218400000 / 119125834289))
            )
          )
        )
        (.split 0 (1 / 2)
          (.retain (28332860760000 / 161170246391))
          (.split 1 (1 / 2)
            (.retain (645619896000000 / 2739894188647))
            (.split 2 (1 / 2)
              (.retain (968193395520000 / 2739894188647))
              (.retain (94424164320000 / 249081289877))
            )
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (2009763345600000 / 2739894188647))
              (.retain (1451828607840000 / 2739894188647))
            )
            (.retain (980621508000000 / 2739894188647))
          )
          (.split 3 (1 / 2)
            (.retain (52256177760000 / 249081289877))
            (.retain (599533433280000 / 2739894188647))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1763843760480000 / 2739894188647))
              (.retain (946969333920000 / 2739894188647))
            )
            (.retain (575628180240000 / 2739894188647))
          )
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (165771687360000 / 249081289877))
              (.retain (1261071746400000 / 2739894188647))
            )
            (.retain (772604674320000 / 2739894188647))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (206659933440000 / 249081289877))
              (.retain (1712844169440000 / 2739894188647))
            )
            (.split 1 (1 / 2)
              (.retain (1667246702400000 / 2739894188647))
              (.retain (1851124129440000 / 2739894188647))
            )
          )
          (.split 1 (1 / 2)
            (.retain (835225294320000 / 2739894188647))
            (.split 2 (1 / 2)
              (.retain (1284426340320000 / 2739894188647))
              (.retain (209985828000000 / 391413455521))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 0 (1 / 2)
              (.retain (112768112640000 / 249081289877))
              (.retain (1184567245440000 / 2739894188647))
            )
            (.retain (63185363280000 / 249081289877))
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (174655764000000 / 391413455521))
              (.retain (55692724800000 / 119125834289))
            )
            (.split 2 (1 / 2)
              (.retain (1436535900480000 / 2739894188647))
              (.retain (115870658880000 / 249081289877))
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (71756209403 / 50000000000000) := by
  decide +kernel

end C100S004
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
