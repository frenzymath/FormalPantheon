import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C103S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C103S003

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(136397197 / 833500000), (37501 / 250000), (54459659 / 416750000)],
    ![(126251 / 500000), (43 / 400), (43 / 400)],
    ![(104999 / 500000), (37501 / 250000), (16249 / 250000)],
    ![(104999 / 500000), (37501 / 250000), (43 / 400)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (758 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (2576 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (2576 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (379 / 1667));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (758 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (2576 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (2576 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (379 / 1667));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).2 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.zeroFace 9 0
    (.split 0 (2517959 / 4356660)
      (.split 3 (1838701 / 4356660)
        (.zeroFace 13 0
          (.retain 404)
        )
        (.split 4 (18751 / 21252)
          (.zeroFace 13 0
            (.retain 319)
          )
          (.retain 470)
        )
      )
      (.zeroFace 13 1
        (.retain 404)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 2 3 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = 0 := by
  decide +kernel

end C103S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
