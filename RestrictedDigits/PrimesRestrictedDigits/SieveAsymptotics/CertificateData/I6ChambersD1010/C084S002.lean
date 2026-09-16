import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C084S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C084S002

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(244997 / 1500000), (244997 / 1500000), (147503 / 1500000)],
    ![(23001 / 100000), (16249 / 125000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 2000000)],
    ![(410011 / 2000000), (309993 / 2000000), (180001 / 2000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (47297950548480000 / 125067512150729))
              (.retain (58710599400960000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (85694579758080000 / 125067512150729))
                (.retain (81912498739200000 / 125067512150729))
              )
              (.retain (70523046466560000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (60264841052160000 / 125067512150729))
              (.retain (54640526976000000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (47447145446400000 / 125067512150729))
              (.retain (58897093017600000 / 125067512150729))
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (30958520509440000 / 125067512150729))
              (.retain (43124535820800000 / 125067512150729))
            )
            (.retain (22772397047040000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.retain (33455905885440000 / 125067512150729))
            (.retain (31768583742720000 / 125067512150729))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (18179521643520000 / 125067512150729))
            (.retain (18875682178560000 / 125067512150729))
          )
          (.retain (17019319092480000 / 125067512150729))
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (29733606362880000 / 125067512150729))
            (.retain (11072483205120000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.retain (18698531662080000 / 125067512150729))
            (.retain (17158710055680000 / 125067512150729))
          )
        )
      )
    )
    (.split 2 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (30156280704000000 / 125067512150729))
            (.retain (27645237342720000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (73321541867520000 / 125067512150729))
              (.retain (60429327575040000 / 125067512150729))
            )
            (.retain (39746915447040000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.retain (14355645799680000 / 125067512150729))
          (.split 2 (1 / 2)
            (.retain (14462266728960000 / 125067512150729))
            (.retain (13206745059840000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (860418408960000 / 2908546794203))
              (.retain (62818388259840000 / 125067512150729))
            )
            (.retain (24091801574400000 / 125067512150729))
          )
          (.retain (12685087463040000 / 125067512150729))
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (34647968862720000 / 125067512150729))
              (.retain (59293354152960000 / 125067512150729))
            )
            (.retain (22329284520960000 / 125067512150729))
          )
          (.retain (10440836058240000 / 125067512150729))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 3) (i6D1006LeafValid 2 2 3) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3) root = (80203464877 / 100000000000000) := by
  decide +kernel

end C084S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
