import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C034S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C034S001

/-!
# exact I6 chamber certificate C034S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C034S002

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 5 (9546 / 17425) C034S000.tree C034S001.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 0) (i6D1006LeafValid 1 1 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C034S000.root_eq_path] using C034S000.valid)
    (by simpa only [C034S001.root_eq_path] using C034S001.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0) root = (5309 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C034S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (9546 / 17425));
       T) = (5309 / 100000000000000) := by
    simpa only [C034S000.root_eq_path] using C034S000.replay
  have h1 : C034S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (9546 / 17425));
       T) = 0 := by
    simpa only [C034S001.root_eq_path] using C034S001.replay
  calc
    _ = ((5309 / 100000000000000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C034S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
