import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C103S011
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C103S011

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(37501 / 250000), (37501 / 250000), (37501 / 250000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(37501 / 250000), (37501 / 250000), (12499 / 100000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 3485));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (758 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 3485));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (2576 / 3485)
    (.zeroFace 1 0
      (.split 1 (1 / 2)
        (.split 3 (1288 / 1667)
          (.split 5 (1 / 2)
            (.exclude 13)
            (.zeroFace 9 0
              (.exclude 13)
            )
          )
          (.exclude 13)
        )
        (.exclude 13)
      )
    )
    (.split 0 (379 / 1667)
      (.split 4 (1 / 2)
        (.split 5 (379 / 1667)
          (.split 0 (26696287 / 57954204)
            (.split 3 (1838701 / 4356660)
              (.zeroFace 13 0
                (.retain 481)
              )
              (.split 4 (18751 / 21252)
                (.zeroFace 13 0
                  (.retain 426)
                )
                (.split 4 (1 / 2)
                  (.split 2 (1 / 2)
                    (.split 5 (1 / 2)
                      (.split 4 (1 / 2)
                        (.retain (44407071792000000 / 146981809618037))
                        (.split 3 (1 / 2)
                          (.retain (54260032412700000 / 146981809618037))
                          (.retain (65995743393900000 / 146981809618037))
                        )
                      )
                      (.split 4 (1 / 2)
                        (.retain (55486016794800000 / 146981809618037))
                        (.split 3 (1 / 2)
                          (.retain (62477506030500000 / 146981809618037))
                          (.retain (69754011198300000 / 146981809618037))
                        )
                      )
                    )
                    (.split 3 (1 / 2)
                      (.split 2 (1 / 2)
                        (.retain (62095648631400000 / 146981809618037))
                        (.retain (67532210501400000 / 146981809618037))
                      )
                      (.split 0 (1 / 2)
                        (.split 4 (1 / 2)
                          (.retain (68768891234100000 / 146981809618037))
                          (.retain (78771725485200000 / 146981809618037))
                        )
                        (.split 2 (1 / 2)
                          (.retain (67246751695500000 / 146981809618037))
                          (.retain (73001993847300000 / 146981809618037))
                        )
                      )
                    )
                  )
                  (.split 3 (1 / 2)
                    (.split 3 (1 / 2)
                      (.split 5 (1 / 2)
                        (.split 2 (1 / 2)
                          (.retain (81290898854100000 / 146981809618037))
                          (.retain (76759809995700000 / 146981809618037))
                        )
                        (.retain (71128768059450000 / 146981809618037))
                      )
                      (.split 2 (1 / 2)
                        (.split 4 (1 / 2)
                          (.retain (87632284812300000 / 146981809618037))
                          (.retain (89788947193800000 / 146981809618037))
                        )
                        (.split 0 (1 / 2)
                          (.retain (87286578011100000 / 146981809618037))
                          (.retain (80443775628000000 / 146981809618037))
                        )
                      )
                    )
                    (.split 0 (1 / 2)
                      (.split 4 (1 / 2)
                        (.split 2 (1 / 2)
                          (.retain (107133936251400000 / 146981809618037))
                          (.retain (112122912486600000 / 146981809618037))
                        )
                        (.split 3 (1 / 2)
                          (.retain (119691666281700000 / 146981809618037))
                          (.split 0 (1 / 2)
                            (.retain (143739772477200000 / 146981809618037))
                            (.retain (129009861253800000 / 146981809618037))
                          )
                        )
                      )
                      (.split 0 (1 / 2)
                        (.split 4 (1 / 2)
                          (.retain (98295012796500000 / 146981809618037))
                          (.retain (102564393866100000 / 146981809618037))
                        )
                        (.split 2 (1 / 2)
                          (.retain (92820950526600000 / 146981809618037))
                          (.retain (87409892349900000 / 146981809618037))
                        )
                      )
                    )
                  )
                )
              )
            )
            (.zeroFace 13 1
              (.retain 507)
            )
          )
          (.zeroFace 9 0
            (.split 0 (26696287 / 57954204)
              (.split 3 (31257917 / 57954204)
                (.zeroFace 13 0
                  (.retain 507)
                )
                (.split 4 (1838701 / 4356660)
                  (.zeroFace 13 0
                    (.retain 481)
                  )
                  (.retain 625)
                )
              )
              (.zeroFace 13 1
                (.retain 507)
              )
            )
          )
        )
        (.zeroFace 9 0
          (.split 2 (26696287 / 57954204)
            (.split 4 (26696287 / 57954204)
              (.split 5 (26696287 / 57954204)
                (.retain 654)
                (.zeroFace 13 0
                  (.retain 507)
                )
              )
              (.zeroFace 13 0
                (.retain 507)
              )
            )
            (.zeroFace 13 3
              (.retain 507)
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 5 (379 / 1667)
          (.exclude 13)
          (.zeroFace 9 0
            (.exclude 13)
          )
        )
        (.exclude 13)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 2 3 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = (67782980021 / 100000000000000) := by
  decide +kernel

end C103S011
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
