import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S020
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S020

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(672519 / 4000000), (342491 / 4000000), (342491 / 4000000)],
    ![(1592559 / 8000000), (24099 / 320000), (24099 / 320000)],
    ![(377513 / 2000000), (212499 / 2000000), (16249 / 250000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (728414574796800000 / 561658568377843))
              (.retain (629309830533120000 / 561658568377843))
            )
            (.retain (430513656053760000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (313212270919680000 / 561658568377843))
            (.retain (301104493424640000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (169289546296320000 / 561658568377843))
          (.retain (159517914071040000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (723155548631040000 / 561658568377843))
              (.retain (614918024663040000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (490748722237440000 / 561658568377843))
              (.retain (354590060175360000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (308899401338880000 / 561658568377843))
              (.retain (438762706882560000 / 561658568377843))
            )
            (.retain (228181845565440000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (157714618982400000 / 561658568377843))
          (.retain (153484975457280000 / 561658568377843))
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (703584065802240000 / 561658568377843))
              (.retain (598357539348480000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (344051569336320000 / 561658568377843))
              (.retain (477199234252800000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.retain (279274877798400000 / 561658568377843))
            (.retain (276291809372160000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (145939552496640000 / 561658568377843))
          (.retain (150169196021760000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (513354885765120000 / 561658568377843))
            (.retain (269830636001280000 / 561658568377843))
          )
          (.split 5 (1 / 2)
            (.retain (496468774103040000 / 561658568377843))
            (.retain (254259248302080000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (136393774433280000 / 561658568377843))
          (.retain (130704932459520000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (24346020933 / 25000000000000) := by
  decide +kernel

end C059S020
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
