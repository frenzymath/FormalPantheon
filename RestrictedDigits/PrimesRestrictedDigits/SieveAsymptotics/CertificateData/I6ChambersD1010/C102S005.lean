import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C102S005
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C102S005

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

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
  (.zeroFace 0 1
    (.split 1 (82507 / 115005)
      (.split 3 (82507 / 115005)
        (.zeroFace 1 0
          (.exclude 9)
        )
        (.split 4 (82507 / 115005)
          (.zeroFace 1 0
            (.zeroFace 9 1
              (.retain 0)
            )
          )
          (.zeroFace 9 3
            (.retain 0)
          )
        )
      )
      (.split 2 (82507 / 115005)
        (.split 4 (82507 / 115005)
          (.zeroFace 1 0
            (.zeroFace 9 0
              (.retain 0)
            )
          )
          (.zeroFace 9 0
            (.retain 0)
          )
        )
        (.zeroFace 9 3
          (.retain 0)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 4) (i6D1006LeafValid 2 3 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4) root = 0 := by
  decide +kernel

end C102S005
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
