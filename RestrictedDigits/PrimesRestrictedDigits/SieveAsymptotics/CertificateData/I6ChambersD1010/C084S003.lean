import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C084S001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C084S002

/-!
# exact I6 chamber certificate C084S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C084S003

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(244997 / 1500000), (244997 / 1500000), (147503 / 1500000)],
    ![(23001 / 100000), (16249 / 125000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 2000000)],
    ![(180001 / 1000000), (180001 / 1000000), (23001 / 200000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 4 (1 / 2) C084S001.tree C084S002.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 3) (i6D1006LeafValid 2 2 3) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C084S001.root_eq_path] using C084S001.valid)
    (by simpa only [C084S002.root_eq_path] using C084S002.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3) root = (151076228433 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C084S001.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
       T) = (17718190889 / 25000000000000) := by
    simpa only [C084S001.root_eq_path] using C084S001.replay
  have h1 : C084S002.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
       T) = (80203464877 / 100000000000000) := by
    simpa only [C084S002.root_eq_path] using C084S002.replay
  calc
    _ = ((17718190889 / 25000000000000) : Rat) + (80203464877 / 100000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C084S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
