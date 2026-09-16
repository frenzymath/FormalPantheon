import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C034S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C034S001

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (319999 / 2500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (9546 / 17425));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (9546 / 17425));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.zeroFace 1 0
    (.split 0 (1895 / 23637)
      (.split 3 (21742 / 23637)
        (.exclude 8)
        (.split 4 (6212 / 7879)
          (.exclude 8)
          (.zeroFace 6 0
            (.exclude 8)
          )
        )
      )
      (.exclude 8)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 0) (i6D1006LeafValid 1 1 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 0) root = 0 := by
  decide +kernel

end C034S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
