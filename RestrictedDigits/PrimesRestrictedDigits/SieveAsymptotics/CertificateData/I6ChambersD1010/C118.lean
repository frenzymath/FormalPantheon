import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C118S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C118S001

/-!
# exact I6 chamber certificate C118
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C118

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 2 (2 / 3) C118S000.tree C118S001.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 2 4 1) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C118S000.root_eq_path] using C118S000.valid)
    (by simpa only [C118S001.root_eq_path] using C118S001.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = (29418063 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C118S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       T) = (29418063 / 100000000000000) := by
    simpa only [C118S000.root_eq_path] using C118S000.replay
  have h1 : C118S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
       T) = 0 := by
    simpa only [C118S001.root_eq_path] using C118S001.replay
  calc
    _ = ((29418063 / 100000000000000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C118
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
