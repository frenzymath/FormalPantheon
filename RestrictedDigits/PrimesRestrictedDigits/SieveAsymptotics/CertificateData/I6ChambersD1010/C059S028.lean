import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S028
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S028

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(672519 / 4000000), (342491 / 4000000), (342491 / 4000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (547616696647680000 / 561658568377843))
              (.retain (468811842785280000 / 561658568377843))
            )
            (.retain (319865923307520000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (228058409687040000 / 561658568377843))
            (.retain (221585072578560000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (121803665080320000 / 561658568377843))
          (.retain (116218737146880000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (543677614571520000 / 561658568377843))
              (.retain (458334941552640000 / 561658568377843))
            )
            (.retain (314701890416640000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (274604526213120000 / 561658568377843))
            (.retain (167207979939840000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (113936570910720000 / 561658568377843))
          (.retain (111972262302720000 / 561658568377843))
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (543954551500800000 / 561658568377843))
              (.retain (465713104711680000 / 561658568377843))
            )
            (.retain (317612295567360000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (218676782315520000 / 561658568377843))
            (.retain (222656119142400000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (120556664939520000 / 561658568377843))
          (.retain (114971736960000000 / 561658568377843))
        )
      )
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (536197151600640000 / 561658568377843))
              (.retain (445722321530880000 / 561658568377843))
            )
            (.retain (307909325813760000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (162768375244800000 / 561658568377843))
            (.retain (263802651125760000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (107235500544000000 / 561658568377843))
          (.retain (106649953827840000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (37169887409 / 50000000000000) := by
  decide +kernel

end C059S028
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
