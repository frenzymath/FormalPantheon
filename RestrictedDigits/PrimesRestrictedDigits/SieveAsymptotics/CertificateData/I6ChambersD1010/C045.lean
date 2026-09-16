import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C045
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C045

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

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
    (.split 2 (34999 / 115005)
      (.split 4 (34999 / 115005)
        (.split 5 (34999 / 115005)
          (.split 2 (180001 / 240018)
            (.split 4 (180001 / 240018)
              (.split 5 (180001 / 240018)
                (.zeroFace 3 0
                  (.split 0 (59992 / 60017)
                    (.split 4 (25 / 60017)
                      (.split 5 (25 / 60017)
                        (.retain 230)
                        (.zeroFace 9 0
                          (.retain 231)
                        )
                      )
                      (.zeroFace 9 0
                        (.retain 231)
                      )
                    )
                    (.split 1 (59992 / 60017)
                      (.split 5 (25 / 60017)
                        (.retain 229)
                        (.zeroFace 9 0
                          (.retain 229)
                        )
                      )
                      (.retain 229)
                    )
                  )
                )
                (.split 0 (59992 / 60017)
                  (.zeroFace 9 0
                    (.retain 231)
                  )
                  (.split 1 (59992 / 420019)
                    (.zeroFace 9 0
                      (.retain 199)
                    )
                    (.split 2 (59992 / 60017)
                      (.zeroFace 9 0
                        (.retain 219)
                      )
                      (.split 0 (1 / 2)
                        (.split 3 (1 / 2)
                          (.retain (129161255814339451875 / 607260406048739992))
                          (.split 4 (1 / 2)
                            (.retain (33861811680554675625 / 151815101512184998))
                            (.retain (16984186472813883750 / 75907550756092499))
                          )
                        )
                        (.split 0 (1 / 2)
                          (.retain (16508530272881790000 / 75907550756092499))
                          (.retain (65961481512237103125 / 303630203024369996))
                        )
                      )
                    )
                  )
                )
              )
              (.split 0 (375008 / 780071)
                (.split 3 (45007 / 80006)
                  (.exclude 9)
                  (.split 4 (135021 / 180001)
                    (.exclude 9)
                    (.zeroFace 6 0
                      (.exclude 9)
                    )
                  )
                )
                (.split 0 (5849752429 / 19688810644)
                  (.zeroFace 9 0
                    (.retain 189)
                  )
                  (.split 1 (59992 / 420019)
                    (.zeroFace 9 0
                      (.retain 188)
                    )
                    (.split 2 (59992 / 60017)
                      (.zeroFace 9 0
                        (.retain 210)
                      )
                      (.split 2 (1 / 2)
                        (.split 5 (1 / 2)
                          (.retain (5188727428245335708870625 / 24292238023167745899976))
                          (.retain (2463930796610042447810625 / 12146119011583872949988))
                        )
                        (.retain (20165916646524101680771875 / 97168952092670983599904))
                      )
                    )
                  )
                )
              )
            )
            (.split 0 (185003 / 320024)
              (.split 3 (45007 / 80006)
                (.split 2 (1035045 / 1275013)
                  (.split 4 (360027 / 420019)
                    (.split 5 (360027 / 420019)
                      (.retain (24004700191815786998855668125 / 123426656433180953942867104))
                      (.zeroFace 9 0
                        (.retain 183)
                      )
                    )
                    (.zeroFace 9 0
                      (.retain 180)
                    )
                  )
                  (.zeroFace 9 3
                    (.retain 177)
                  )
                )
                (.split 4 (405063 / 780071)
                  (.split 2 (1035045 / 1275013)
                    (.split 4 (13839058215 / 19688810644)
                      (.split 5 (360027 / 420019)
                        (.retain (478977337979650932179177176875 / 2460169852120538172766439216))
                        (.zeroFace 9 0
                          (.retain 183)
                        )
                      )
                      (.zeroFace 9 0
                        (.retain 180)
                      )
                    )
                    (.zeroFace 9 3
                      (.retain 177)
                    )
                  )
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
              )
              (.split 2 (120009 / 180001)
                (.split 4 (1035045 / 1275013)
                  (.split 5 (360027 / 420019)
                    (.retain (18191962638376881166490625 / 99869154304700584879712))
                    (.zeroFace 9 0
                      (.retain 161)
                    )
                  )
                  (.zeroFace 9 0
                    (.retain 149)
                  )
                )
                (.zeroFace 9 3
                  (.retain 141)
                )
              )
            )
          )
          (.zeroFace 1 0
            (.split 0 (185003 / 320024)
              (.split 3 (135021 / 320024)
                (.exclude 9)
                (.split 4 (45007 / 80006)
                  (.exclude 9)
                  (.zeroFace 6 0
                    (.exclude 9)
                  )
                )
              )
              (.exclude 9)
            )
          )
        )
        (.zeroFace 1 0
          (.split 2 (185003 / 320024)
            (.split 4 (185003 / 320024)
              (.split 5 (185003 / 320024)
                (.zeroFace 6 0
                  (.exclude 9)
                )
                (.exclude 9)
              )
              (.exclude 9)
            )
            (.exclude 9)
          )
        )
      )
      (.zeroFace 1 3
        (.exclude 9)
      )
    )
    (.zeroFace 0 1
      (.exclude 1)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 1) (i6D1006LeafValid 1 6 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 1) root = (18184640943 / 100000000000000) := by
  decide +kernel

end C045
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
