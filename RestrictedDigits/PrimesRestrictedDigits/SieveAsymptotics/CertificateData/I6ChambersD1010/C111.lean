import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C111
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C111

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(16249 / 250000), (16249 / 250000), (16249 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (2 / 3)
    (.zeroFace 5 0
      (.zeroFace 6 0
        (.split 2 (758 / 24395)
          (.split 4 (758 / 24395)
            (.split 5 (758 / 24395)
              (.zeroFace 10 0
                (.retain 35)
              )
              (.retain 27)
            )
            (.retain 18)
          )
          (.retain 9)
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 5 0
        (.zeroFace 6 3
          (.retain 0)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 0) (i6D1006LeafValid 2 2 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0) root = 0 := by
  decide +kernel

end C111
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
