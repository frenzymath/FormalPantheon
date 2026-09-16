import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S003

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(43 / 200), (180001 / 1500000), (180001 / 1500000)],
    ![(126251 / 500000), (43 / 400), (43 / 400)],
    ![(212499 / 1000000), (147503 / 1000000), (212499 / 2000000)],
    ![(180001 / 750000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (63756 / 82507));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (63756 / 82507));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 5 (7503 / 82507)
    (.zeroFace 15 0
      (.retain 526)
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.retain (150701509800000 / 879351602501))
        (.split 2 (1 / 2)
          (.retain (215651804040000 / 879351602501))
          (.retain (313401085200000 / 879351602501))
        )
      )
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.retain (263451451320000 / 879351602501))
          (.retain (366255227880000 / 879351602501))
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (518953790160000 / 879351602501))
            (.retain (678860796960000 / 879351602501))
          )
          (.retain (472856902560000 / 879351602501))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (1758282489 / 25000000000000) := by
  decide +kernel

end C100S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
