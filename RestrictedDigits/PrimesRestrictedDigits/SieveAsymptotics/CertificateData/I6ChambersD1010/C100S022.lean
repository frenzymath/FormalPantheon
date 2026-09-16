import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C100S020
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C100S021

/-!
# exact I6 chamber certificate C100S022
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S022

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

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
  .split 5 (1 / 2) C100S020.tree C100S021.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C100S020.root_eq_path] using C100S020.valid)
    (by simpa only [C100S021.root_eq_path] using C100S021.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (273299208497 / 50000000000000) := by
  rw [root_eq_path]
  have h0 : C100S020.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
       T) = (273299208497 / 50000000000000) := by
    simpa only [C100S020.root_eq_path] using C100S020.replay
  have h1 : C100S021.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
       T) = 0 := by
    simpa only [C100S021.root_eq_path] using C100S021.replay
  calc
    _ = ((273299208497 / 50000000000000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C100S022
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
