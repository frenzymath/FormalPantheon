import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C084S000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C084S005

/-!
# exact I6 chamber certificate C084S006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C084S006

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(244997 / 1500000), (244997 / 1500000), (147503 / 1500000)],
    ![(23001 / 100000), (16249 / 125000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 5 (50009 / 115005) C084S000.tree C084S005.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 3) (i6D1006LeafValid 2 2 3) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C084S000.root_eq_path] using C084S000.valid)
    (by simpa only [C084S005.root_eq_path] using C084S005.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3) root = (151076228433 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C084S000.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (50009 / 115005));
       T) = 0 := by
    simpa only [C084S000.root_eq_path] using C084S000.replay
  have h1 : C084S005.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 3)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (64996 / 115005));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (50009 / 115005));
       T) = (151076228433 / 100000000000000) := by
    simpa only [C084S005.root_eq_path] using C084S005.replay
  calc
    _ = (0 : Rat) + (151076228433 / 100000000000000) :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C084S006
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
