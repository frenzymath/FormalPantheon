import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C035S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C035S001

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(70833 / 500000), (70833 / 500000), (70833 / 500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(287501 / 2000000), (287501 / 2000000), (137497 / 1000000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (379 / 6970));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (379 / 6970));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (379 / 27880)
    (.split 4 (18334 / 24395)
      (.split 2 (284998 / 345015)
        (.split 4 (179920 / 600039)
          (.split 5 (284998 / 345015)
            (.split 0 (1649830517 / 1650527517)
              (.split 3 (174250 / 395572047)
                (.retain (2022770630337912000 / 8993893451786071))
                (.split 4 (25 / 120034)
                  (.retain (3433858272 / 15161137))
                  (.zeroFace 9 0
                    (.retain 231)
                  )
                )
              )
              (.split 4 (1 / 2)
                (.retain (498208861814555304000000 / 2252304521064910077527))
                (.retain (509168026010018160000000 / 2252304521064910077527))
              )
            )
            (.zeroFace 8 0
              (.split 0 (1649830517 / 1650527517)
                (.split 3 (697000 / 1650527517)
                  (.retain 229)
                  (.split 4 (174250 / 395572047)
                    (.retain 230)
                    (.zeroFace 9 0
                      (.retain 231)
                    )
                  )
                )
                (.retain 228)
              )
            )
          )
          (.zeroFace 8 0
            (.split 2 (1649830517 / 1650527517)
              (.split 4 (1649830517 / 1650527517)
                (.split 5 (1649830517 / 1650527517)
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
    (.split 2 (284998 / 345015)
      (.split 4 (284998 / 345015)
        (.split 5 (284998 / 345015)
          (.retain (6924102398215704000000 / 31052835960510528233))
          (.zeroFace 8 0
            (.retain 227)
          )
        )
        (.zeroFace 8 0
          (.retain 227)
        )
      )
      (.zeroFace 8 3
        (.retain 227)
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 1 1) (i6D1006LeafValid 1 1 1) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 1 1) root = (540893353 / 50000000000000) := by
  decide +kernel

end C035S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
