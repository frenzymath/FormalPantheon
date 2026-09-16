import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C082S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C082S001

/-!
# exact I6 chamber certificate C082S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C082S002

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 4 (9546 / 17425) C082S000.tree C082S001.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 0) (i6D1006LeafValid 2 2 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C082S000.root_eq_path] using C082S000.valid)
    (by simpa only [C082S001.root_eq_path] using C082S001.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0) root = (34030625897 / 20000000000000) := by
  rw [root_eq_path]
  have h0 : C082S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
       T) = (3813789379 / 5000000000000) := by
    simpa only [C082S000.root_eq_path] using C082S000.replay
  have h1 : C082S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
       T) = (18775468381 / 20000000000000) := by
    simpa only [C082S001.root_eq_path] using C082S001.replay
  calc
    _ = ((3813789379 / 5000000000000) : Rat) + (18775468381 / 20000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C082S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
