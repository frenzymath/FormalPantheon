import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C046S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C046S031

/-!
# exact I6 chamber certificate C046
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

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
  .split 0 (82507 / 115005) C046S000.tree C046S031.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C046S000.root_eq_path] using C046S000.valid)
    (by simpa only [C046S031.root_eq_path] using C046S031.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (1173758807207 / 50000000000000) := by
  rw [root_eq_path]
  have h0 : C046S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (82507 / 115005));
       T) = 0 := by
    simpa only [C046S000.root_eq_path] using C046S000.replay
  have h1 : C046S031.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       T) = (1173758807207 / 50000000000000) := by
    simpa only [C046S031.root_eq_path] using C046S031.replay
  calc
    _ = (0 : Rat) + (1173758807207 / 50000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C046
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
