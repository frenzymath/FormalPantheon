import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C051S006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C051S007

/-!
# exact I6 chamber certificate C051S008
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C051S008

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(82507 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(23001 / 200000), (23001 / 200000), (16249 / 250000)],
    ![(147503 / 1500000), (147503 / 1500000), (147503 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 4 (1 / 2) C051S006.tree C051S007.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 5) (i6D1006LeafValid 2 0 5) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C051S006.root_eq_path] using C051S006.valid)
    (by simpa only [C051S007.root_eq_path] using C051S007.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5) root = (32402066943 / 20000000000000) := by
  rw [root_eq_path]
  have h0 : C051S006.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
       T) = (78575272729 / 100000000000000) := by
    simpa only [C051S006.root_eq_path] using C051S006.replay
  have h1 : C051S007.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 5)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (50009 / 82507));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
       T) = (41717530993 / 50000000000000) := by
    simpa only [C051S007.root_eq_path] using C051S007.replay
  calc
    _ = ((78575272729 / 100000000000000) : Rat) + (41717530993 / 50000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C051S008
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
