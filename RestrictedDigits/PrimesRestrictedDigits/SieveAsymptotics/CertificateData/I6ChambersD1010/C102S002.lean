import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C102S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C102S001

/-!
# exact I6 chamber certificate C102S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C102S002

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(55499 / 300000), (180001 / 1500000), (180001 / 1500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 3 (82507 / 115005) C102S000.tree C102S001.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 4) (i6D1006LeafValid 2 3 4) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C102S000.root_eq_path] using C102S000.valid)
    (by simpa only [C102S001.root_eq_path] using C102S001.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4) root = (87384961833 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C102S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (82507 / 115005));
       T) = 0 := by
    simpa only [C102S000.root_eq_path] using C102S000.replay
  have h1 : C102S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
       T) = (87384961833 / 100000000000000) := by
    simpa only [C102S001.root_eq_path] using C102S001.replay
  calc
    _ = (0 : Rat) + (87384961833 / 100000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C102S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
