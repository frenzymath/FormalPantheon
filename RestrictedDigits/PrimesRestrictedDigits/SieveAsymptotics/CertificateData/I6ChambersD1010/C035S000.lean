import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C035S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C035S000

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(287501 / 2000000), (287501 / 2000000), (137497 / 1000000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (379 / 6970));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (379 / 6970));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 3 (4773 / 6970)
    (.split 5 (4394 / 10455)
      (.split 4 (8788 / 14849)
        (.split 2 (284998 / 345015)
          (.split 4 (1199943482 / 2091135915)
            (.split 5 (139996 / 200013)
              (.split 0 (395397797 / 395572047)
                (.split 4 (25 / 120034)
                  (.split 5 (25 / 120034)
                    (.retain (787121687376000 / 3515727299773))
                    (.zeroFace 9 0
                      (.retain 229)
                    )
                  )
                  (.zeroFace 9 0
                    (.retain 229)
                  )
                )
                (.split 1 (395397797 / 395572047)
                  (.split 5 (25 / 120034)
                    (.retain (3540138443280000 / 15817098073391))
                    (.zeroFace 9 0
                      (.retain 228)
                    )
                  )
                  (.split 4 (1 / 2)
                    (.split 5 (1 / 2)
                      (.retain (2055855823610698764000000 / 9383022842451024244553))
                      (.retain (2094712308450527040000000 / 9383022842451024244553))
                    )
                    (.retain (2116146158322674580000000 / 9383022842451024244553))
                  )
                )
              )
              (.zeroFace 8 0
                (.split 0 (395397797 / 395572047)
                  (.split 3 (174250 / 395572047)
                    (.split 5 (395397797 / 395572047)
                      (.zeroFace 9 0
                        (.retain 229)
                      )
                      (.retain 228)
                    )
                    (.zeroFace 9 0
                      (.retain 229)
                    )
                  )
                  (.split 2 (395397797 / 395572047)
                    (.split 5 (395397797 / 395572047)
                      (.zeroFace 9 0
                        (.retain 228)
                      )
                      (.retain 228)
                    )
                    (.retain 228)
                  )
                )
              )
            )
            (.zeroFace 8 0
              (.split 2 (395397797 / 395572047)
                (.split 4 (395397797 / 395572047)
                  (.split 5 (395397797 / 395572047)
                    (.zeroFace 9 0
                      (.retain 229)
                    )
                    (.retain 228)
                  )
                  (.retain 228)
                )
                (.retain 228)
              )
            )
          )
          (.zeroFace 8 3
            (.retain 227)
          )
        )
        (.zeroFace 6 0
          (.exclude 8)
        )
      )
      (.zeroFace 5 0
        (.zeroFace 6 0
          (.exclude 8)
        )
      )
    )
    (.split 4 (18334 / 24395)
      (.split 5 (8788 / 14849)
        (.split 2 (284998 / 345015)
          (.split 4 (179920 / 600039)
            (.split 5 (1199943482 / 2091135915)
              (.split 0 (395397797 / 395572047)
                (.split 4 (25 / 120034)
                  (.split 5 (25 / 120034)
                    (.retain (573428881152000 / 2545981854319))
                    (.zeroFace 9 0
                      (.retain 231)
                    )
                  )
                  (.zeroFace 9 0
                    (.retain 231)
                  )
                )
                (.split 1 (395397797 / 395572047)
                  (.split 5 (25 / 120034)
                    (.retain (5651876304113832000 / 25165003034765081))
                    (.zeroFace 9 0
                      (.retain 229)
                    )
                  )
                  (.split 4 (1 / 2)
                    (.split 5 (1 / 2)
                      (.retain (3273397174220106641292000000 / 14928389342339579573083823))
                      (.retain (3336275056667042568780000000 / 14928389342339579573083823))
                    )
                    (.split 0 (1 / 2)
                      (.split 3 (1 / 2)
                        (.retain (3377394376605654549768000000 / 14928389342339579573083823))
                        (.retain (78766042446094608072000000 / 347171845170687897048461))
                      )
                      (.retain (3369005415461063639664000000 / 14928389342339579573083823))
                    )
                  )
                )
              )
              (.zeroFace 8 0
                (.split 0 (395397797 / 395572047)
                  (.split 3 (174250 / 395572047)
                    (.split 5 (395397797 / 395572047)
                      (.zeroFace 9 0
                        (.retain 231)
                      )
                      (.retain 230)
                    )
                    (.zeroFace 9 0
                      (.retain 231)
                    )
                  )
                  (.split 2 (395397797 / 395572047)
                    (.split 5 (395397797 / 395572047)
                      (.zeroFace 9 0
                        (.retain 229)
                      )
                      (.retain 229)
                    )
                    (.retain 229)
                  )
                )
              )
            )
            (.zeroFace 8 0
              (.split 2 (395397797 / 395572047)
                (.split 4 (395397797 / 395572047)
                  (.split 5 (395397797 / 395572047)
                    (.zeroFace 9 0
                      (.retain 231)
                    )
                    (.retain 230)
                  )
                  (.retain 229)
                )
                (.retain 228)
              )
            )
          )
          (.zeroFace 8 3
            (.retain 227)
          )
        )
        (.zeroFace 6 0
          (.exclude 8)
        )
      )
      (.zeroFace 6 0
        (.exclude 8)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 1) (i6D1006LeafValid 1 1 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1) root = (18812848453 / 100000000000000) := by
  decide +kernel

end C035S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
