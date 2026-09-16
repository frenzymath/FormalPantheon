import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C102S004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C102S005

/-!
# exact I6 chamber certificate C102
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C102

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

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
  .split 2 (2 / 3) C102S004.tree C102S005.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 4) (i6D1006LeafValid 2 3 4) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C102S004.root_eq_path] using C102S004.valid)
    (by simpa only [C102S005.root_eq_path] using C102S005.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4) root = (87384961833 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C102S004.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       T) = (87384961833 / 100000000000000) := by
    simpa only [C102S004.root_eq_path] using C102S004.replay
  have h1 : C102S005.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
       T) = 0 := by
    simpa only [C102S005.root_eq_path] using C102S005.replay
  calc
    _ = ((87384961833 / 100000000000000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C102
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
