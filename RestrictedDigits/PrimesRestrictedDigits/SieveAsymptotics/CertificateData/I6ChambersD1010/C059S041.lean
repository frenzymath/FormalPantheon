import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C059S001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C059S040

/-!
# exact I6 chamber certificate C059S041
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S041

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(23001 / 100000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 1 (82507 / 115005) C059S001.tree C059S040.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C059S001.root_eq_path] using C059S001.valid)
    (by simpa only [C059S040.root_eq_path] using C059S040.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (236601999279 / 10000000000000) := by
  rw [root_eq_path]
  have h0 : C059S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (82507 / 115005));
       T) = 0 := by
    simpa only [C059S001.root_eq_path] using C059S001.replay
  have h1 : C059S040.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
       T) = (236601999279 / 10000000000000) := by
    simpa only [C059S040.root_eq_path] using C059S040.replay
  calc
    _ = (0 : Rat) + (236601999279 / 10000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C059S041
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
