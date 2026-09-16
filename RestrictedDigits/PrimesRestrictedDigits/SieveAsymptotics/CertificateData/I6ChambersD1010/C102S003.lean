import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C102S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C102S003

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(55499 / 300000), (180001 / 1500000), (180001 / 1500000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (32498 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (32498 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.zeroFace 1 1
    (.retain 0)
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 4) (i6D1006LeafValid 2 3 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4) root = 0 := by
  decide +kernel

end C102S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
