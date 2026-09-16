import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C009S001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C009S002

/-!
# exact I6 chamber certificate C009S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C009S003

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
            let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
                   let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 1 (1501 / 23001) C009S001.tree C009S002.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 0 4 1) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C009S001.root_eq_path] using C009S001.valid)
    (by simpa only [C009S002.root_eq_path] using C009S002.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = 0 := by
  rw [root_eq_path]
  have h0 : C009S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
       let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1501 / 23001));
       T) = 0 := by
    simpa only [C009S001.root_eq_path] using C009S001.replay
  have h1 : C009S002.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
       let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1501 / 23001));
       T) = 0 := by
    simpa only [C009S002.root_eq_path] using C009S002.replay
  calc
    _ = (0 : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C009S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
