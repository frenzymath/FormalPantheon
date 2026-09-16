import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C035S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C035S001

/-!
# exact I6 chamber certificate C035S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C035S002

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 1 (379 / 6970) C035S000.tree C035S001.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 1) (i6D1006LeafValid 1 1 1) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C035S000.root_eq_path] using C035S000.valid)
    (by simpa only [C035S001.root_eq_path] using C035S001.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1) root = (19894635159 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C035S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (379 / 6970));
       T) = (18812848453 / 100000000000000) := by
    simpa only [C035S000.root_eq_path] using C035S000.replay
  have h1 : C035S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (379 / 6970));
       T) = (540893353 / 50000000000000) := by
    simpa only [C035S001.root_eq_path] using C035S001.replay
  calc
    _ = ((18812848453 / 100000000000000) : Rat) + (540893353 / 50000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C035S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
