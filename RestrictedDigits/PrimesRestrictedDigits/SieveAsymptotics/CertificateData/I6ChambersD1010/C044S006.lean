import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C044S004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C044S005

/-!
# exact I6 chamber certificate C044S006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C044S006

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(319999 / 2000000), (319999 / 2000000), (319999 / 2000000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 4 (75002 / 115005) C044S004.tree C044S005.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 0) (i6D1006LeafValid 1 6 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C044S004.root_eq_path] using C044S004.valid)
    (by simpa only [C044S005.root_eq_path] using C044S005.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0) root = (146907451 / 195312500000) := by
  rw [root_eq_path]
  have h0 : C044S004.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (75002 / 115005));
       T) = (146907451 / 195312500000) := by
    simpa only [C044S004.root_eq_path] using C044S004.replay
  have h1 : C044S005.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (75002 / 115005));
       T) = 0 := by
    simpa only [C044S005.root_eq_path] using C044S005.replay
  calc
    _ = ((146907451 / 195312500000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C044S006
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
