import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C027
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C027

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, false]))

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
    (.split 0 (37501 / 115005)
      (.split 3 (310016 / 345015)
        (.split 2 (575002 / 1175041)
          (.split 4 (575002 / 1175041)
            (.split 5 (4394 / 10455)
              (.zeroFace 3 0
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.exclude 9)
        )
        (.split 4 (310016 / 575025)
          (.split 2 (575002 / 1175041)
            (.split 4 (854998 / 1855063)
              (.split 5 (575002 / 1175041)
                (.zeroFace 3 0
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.zeroFace 1 0
            (.exclude 9)
          )
        )
      )
      (.split 0 (12507 / 300008)
        (.split 4 (575002 / 1175041)
          (.split 5 (4394 / 10455)
            (.zeroFace 3 0
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.exclude 9)
        )
        (.split 1 (379 / 6970)
          (.split 5 (4394 / 10455)
            (.zeroFace 3 0
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.zeroFace 3 1
            (.exclude 9)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.split 1 (310016 / 345015)
        (.split 3 (310016 / 345015)
          (.split 2 (287501 / 300008)
            (.split 4 (287501 / 300008)
              (.split 5 (6591 / 6970)
                (.zeroFace 3 0
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
          (.split 4 (77504 / 115005)
            (.split 2 (287501 / 300008)
              (.split 4 (287501 / 300008)
                (.split 5 (287501 / 300008)
                  (.zeroFace 3 0
                    (.exclude 9)
                  )
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.zeroFace 1 0
              (.exclude 9)
            )
          )
        )
        (.split 2 (77504 / 115005)
          (.split 4 (77504 / 115005)
            (.split 2 (287501 / 300008)
              (.split 4 (287501 / 300008)
                (.split 5 (287501 / 300008)
                  (.zeroFace 3 0
                    (.exclude 9)
                  )
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.zeroFace 1 0
              (.exclude 9)
            )
          )
          (.zeroFace 1 2
            (.exclude 9)
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 4 1) (i6D1006LeafValid 1 4 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 4 1) root = 0 := by
  decide +kernel

end C027
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
