import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C134
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C134

abbrev label : i6D691Label :=
  (true, (2, ![true, true, true, true, true]))

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
    (.split 2 (284998 / 345015)
      (.split 4 (284998 / 345015)
        (.split 5 (284998 / 345015)
          (.split 4 (1 / 2)
            (.retain (9661810413240000 / 216183652024913))
            (.retain (3133914269220000 / 216183652024913))
          )
          (.zeroFace 1 0
            (.retain 0)
          )
        )
        (.zeroFace 1 0
          (.retain 0)
        )
      )
      (.zeroFace 1 3
        (.retain 0)
      )
    )
    (.zeroFace 0 1
      (.exclude 1)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 1) (i6D1006LeafValid 2 6 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 1) root = (2632865161 / 100000000000000) := by
  decide +kernel

end C134
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
