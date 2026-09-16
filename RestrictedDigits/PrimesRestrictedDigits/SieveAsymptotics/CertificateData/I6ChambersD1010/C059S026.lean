import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C059S024
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C059S025

/-!
# exact I6 chamber certificate C059S026
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S026

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(147503 / 1000000), (147503 / 1000000), (16249 / 250000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 5 (1 / 2) C059S024.tree C059S025.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C059S024.root_eq_path] using C059S024.valid)
    (by simpa only [C059S025.root_eq_path] using C059S025.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (295785065627 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C059S024.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
       T) = (104621655773 / 50000000000000) := by
    simpa only [C059S024.root_eq_path] using C059S024.replay
  have h1 : C059S025.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
       T) = (86541754081 / 100000000000000) := by
    simpa only [C059S025.root_eq_path] using C059S025.replay
  calc
    _ = ((104621655773 / 50000000000000) : Rat) + (86541754081 / 100000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C059S026
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
