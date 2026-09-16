import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C084S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C084S001

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(244997 / 1500000), (244997 / 1500000), (147503 / 1500000)],
    ![(410011 / 2000000), (309993 / 2000000), (180001 / 2000000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 2000000)],
    ![(180001 / 1000000), (180001 / 1000000), (23001 / 200000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (13586940483840000 / 125067512150729))
            (.retain (13944078501120000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (66030617940480000 / 125067512150729))
              (.retain (39571480650240000 / 125067512150729))
            )
            (.retain (27751909052160000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (38882777402880000 / 125067512150729))
              (.retain (64997563092480000 / 125067512150729))
            )
            (.retain (27235381616640000 / 125067512150729))
          )
          (.retain (13028755743360000 / 125067512150729))
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (42666080348160000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (73188009262080000 / 125067512150729))
              (.retain (62328870190080000 / 125067512150729))
            )
          )
          (.retain (27566186221440000 / 125067512150729))
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (15498683447040000 / 125067512150729))
            (.retain (15990795578880000 / 125067512150729))
          )
          (.retain (14509513537920000 / 125067512150729))
        )
      )
    )
    (.split 4 (1 / 2)
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.retain (12723828215040000 / 125067512150729))
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (62991528261120000 / 125067512150729))
              (.retain (873149322240000 / 2908546794203))
            )
            (.retain (24121262833920000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (22411125504000000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (59571253601280000 / 125067512150729))
              (.retain (35265237742080000 / 125067512150729))
            )
          )
          (.retain (10520085692160000 / 125067512150729))
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (35903818414080000 / 125067512150729))
            (.retain (60529124597760000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (18005126722560000 / 125067512150729))
            (.retain (28870215321600000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.retain (11092833578880000 / 125067512150729))
          (.retain (242684979840000 / 2908546794203))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 3) (i6D1006LeafValid 2 2 3) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3) root = (17718190889 / 25000000000000) := by
  decide +kernel

end C084S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
