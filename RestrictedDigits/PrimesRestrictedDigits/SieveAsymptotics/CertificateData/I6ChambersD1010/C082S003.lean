import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C082S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C082S003

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(1 / 7), (1 / 7), (1 / 7)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 24395));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (758 / 24395));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (64996 / 115005)
    (.split 3 (64996 / 115005)
      (.split 5 (350063 / 830049)
        (.zeroFace 12 0
          (.retain 12)
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (994642915998420000 / 47400587105126291))
            (.retain (10003857699780000 / 1102339235002937))
          )
          (.retain (596297489272110000 / 47400587105126291))
        )
      )
      (.zeroFace 12 0
        (.retain 0)
      )
    )
    (.zeroFace 12 2
      (.retain 0)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 0) (i6D1006LeafValid 2 2 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0) root = (578107267 / 100000000000000) := by
  decide +kernel

end C082S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
