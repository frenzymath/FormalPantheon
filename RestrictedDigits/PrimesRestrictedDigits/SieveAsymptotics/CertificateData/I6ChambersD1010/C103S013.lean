import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C103S011
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C103S012

/-!
# exact I6 chamber certificate C103S013
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C103S013

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(37501 / 250000), (37501 / 250000), (12499 / 100000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .split 2 (758 / 3485) C103S011.tree C103S012.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 2 3 6) root = true := by
  rw [root_eq_path]
  exact valid_split (by decide +kernel) (by decide +kernel)
    (by simpa only [C103S011.root_eq_path] using C103S011.valid)
    (by simpa only [C103S012.root_eq_path] using C103S012.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = (67782980021 / 100000000000000) := by
  rw [root_eq_path]
  have h0 : C103S011.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 3485));
       T) = (67782980021 / 100000000000000) := by
    simpa only [C103S011.root_eq_path] using C103S011.replay
  have h1 : C103S012.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 3485));
       T) = 0 := by
    simpa only [C103S012.root_eq_path] using C103S012.replay
  calc
    _ = ((67782980021 / 100000000000000) : Rat) + 0 :=
      replay_split h0 h1
    _ = _ := by decide +kernel

end C103S013
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
