import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C096
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C096

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

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
      (.split 2 (758 / 24395)
        (.split 4 (9546 / 17425)
          (.split 5 (758 / 24395)
            (.zeroFace 10 0
              (.exclude 13)
            )
            (.exclude 13)
          )
          (.split 0 (239993 / 817542)
            (.split 3 (82507 / 115005)
              (.zeroFace 13 0
                (.retain 29)
              )
              (.split 4 (412535 / 472527)
                (.zeroFace 13 0
                  (.split 0 (340381137 / 650072653)
                    (.split 3 (37502 / 82507)
                      (.retain 251)
                      (.split 4 (309691516 / 650072653)
                        (.retain 381)
                        (.zeroFace 15 0
                          (.retain 507)
                        )
                      )
                    )
                    (.retain 137)
                  )
                )
                (.split 2 (340381137 / 650072653)
                  (.split 4 (63756 / 82507)
                    (.split 5 (45005 / 82507)
                      (.zeroFace 15 0
                        (.retain 654)
                      )
                      (.retain 500)
                    )
                    (.retain 688)
                  )
                  (.retain 278)
                )
              )
            )
            (.zeroFace 13 1
              (.retain 38)
            )
          )
        )
        (.split 0 (32498 / 115005)
          (.split 3 (82507 / 115005)
            (.zeroFace 13 0
              (.retain 0)
            )
            (.split 4 (577549 / 817542)
              (.zeroFace 13 0
                (.retain 10)
              )
              (.retain 21)
            )
          )
          (.zeroFace 13 1
            (.retain 0)
          )
        )
      )
    )
    (.zeroFace 0 1
      (.zeroFace 5 0
        (.split 2 (82507 / 115005)
          (.split 4 (82507 / 115005)
            (.split 5 (82507 / 115005)
              (.zeroFace 13 0
                (.retain 0)
              )
              (.retain 0)
            )
            (.retain 0)
          )
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

end C096
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
