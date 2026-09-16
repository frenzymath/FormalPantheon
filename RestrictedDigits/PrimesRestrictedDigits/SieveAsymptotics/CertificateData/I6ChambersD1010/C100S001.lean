import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S001

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(774274621 / 4129000000), (180001 / 1500000), (180001 / 1500000)],
    ![(212499 / 1000000), (147503 / 1000000), (212499 / 2000000)],
    ![(180001 / 1000000), (180001 / 1000000), (244997 / 2000000)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (82507 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (82507 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.zeroFace 13 0
    (.retain 29)
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = 0 := by
  decide +kernel

end C100S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
