import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C009S003

/-!
# exact I6 chamber certificate C009S004
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C009S004

abbrev label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  .zeroFace 0 1 C009S003.tree

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 0 4 1) root = true := by
  rw [root_eq_path]
  exact valid_zeroFace (by decide +kernel) (by decide +kernel)
    (by simpa only [C009S003.root_eq_path] using C009S003.valid)

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = 0 := by
  rw [root_eq_path]
  have h0 : C009S003.tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1)
      (let T := i6D999OrderedPairRoot;
       let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (2 / 3));
       let T := T.zeroVertexFaceD1001 ((i6D1005ChamberWalls label 4 1) 0) 1;
       T) = 0 := by
    simpa only [C009S003.root_eq_path] using C009S003.replay
  exact replay_zeroFace h0

end C009S004
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
