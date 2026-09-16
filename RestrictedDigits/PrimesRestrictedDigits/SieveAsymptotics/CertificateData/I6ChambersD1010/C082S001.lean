import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C082S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C082S001

abbrev label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1 / 7), (1 / 7), (1 / 7)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (16249 / 250000)],
    ![(290003 / 1250000), (319999 / 2500000), (319999 / 2500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 1 (479986 / 830049)
    (.split 3 (64996 / 115005)
      (.split 5 (250045 / 890043)
        (.zeroFace 12 0
          (.retain 198)
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.split 3 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (643326293116629592960000 / 1567782422822829721481))
                    (.retain (366370255025617124800000 / 1567782422822829721481))
                  )
                  (.retain (197034834141005164640000 / 1567782422822829721481))
                )
                (.split 4 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (645149892092629633920000 / 1567782422822829721481))
                    (.retain (367470572647536588160000 / 1567782422822829721481))
                  )
                  (.retain (198676365333691016800000 / 1567782422822829721481))
                )
              )
              (.split 4 (1 / 2)
                (.split 1 (1 / 2)
                  (.retain (474175748597802641600000 / 1567782422822829721481))
                  (.split 2 (1 / 2)
                    (.retain (596433845895386611840000 / 1567782422822829721481))
                    (.retain (316204235442786933760000 / 1567782422822829721481))
                  )
                )
                (.split 1 (1 / 2)
                  (.retain (193049095790722569440000 / 1567782422822829721481))
                  (.retain (191424473295681429440000 / 1567782422822829721481))
                )
              )
            )
            (.split 4 (1 / 2)
              (.split 4 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (821399310672345144320000 / 1567782422822829721481))
                    (.retain (533536054255155766080000 / 1567782422822829721481))
                  )
                  (.split 1 (1 / 2)
                    (.retain (280662650343355840000 / 985406928235593791))
                    (.retain (409277039009198566080000 / 1567782422822829721481))
                  )
                )
                (.split 1 (1 / 2)
                  (.retain (10443599783465210880000 / 36460056344716970267))
                  (.split 0 (1 / 2)
                    (.retain (495968106047159188800000 / 1567782422822829721481))
                    (.retain (323482403981400137600000 / 1567782422822829721481))
                  )
                )
              )
              (.split 0 (1 / 2)
                (.split 3 (1 / 2)
                  (.retain (203492166529512890400000 / 1567782422822829721481))
                  (.split 4 (1 / 2)
                    (.retain (297418418257422286720000 / 1567782422822829721481))
                    (.retain (113112541947045952640000 / 1567782422822829721481))
                  )
                )
                (.split 0 (1 / 2)
                  (.retain (196848458127861050560000 / 1567782422822829721481))
                  (.retain (193701694323137801920000 / 1567782422822829721481))
                )
              )
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.split 1 (1 / 2)
                (.split 5 (1 / 2)
                  (.retain (12750228704595757760000 / 42372497914130533013))
                  (.retain (190985043079290307680000 / 1567782422822829721481))
                )
                (.split 0 (1 / 2)
                  (.retain (307490991108365790880000 / 1567782422822829721481))
                  (.retain (288728403803593514880000 / 1567782422822829721481))
                )
              )
              (.split 0 (1 / 2)
                (.split 3 (1 / 2)
                  (.retain (304784612058168867520000 / 1567782422822829721481))
                  (.retain (293830985529326003360000 / 1567782422822829721481))
                )
                (.split 1 (1 / 2)
                  (.retain (299285232498427928480000 / 1567782422822829721481))
                  (.retain (279454174237621160960000 / 1567782422822829721481))
                )
              )
            )
            (.split 1 (1 / 2)
              (.split 3 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (591890208986392330560000 / 1567782422822829721481))
                    (.retain (312251101180166368640000 / 1567782422822829721481))
                  )
                  (.retain (4386945577362045600000 / 36460056344716970267))
                )
                (.split 2 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (542060745830041690560000 / 1567782422822829721481))
                    (.retain (276882054764334940480000 / 1567782422822829721481))
                  )
                  (.retain (162927492194439646240000 / 1567782422822829721481))
                )
              )
              (.split 2 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (626670603218225406400000 / 1567782422822829721481))
                    (.retain (368603986279659444160000 / 1567782422822829721481))
                  )
                  (.retain (264473859411989270400000 / 1567782422822829721481))
                )
                (.split 0 (1 / 2)
                  (.retain (147522926414524821440000 / 1567782422822829721481))
                  (.retain (145466234848500235040000 / 1567782422822829721481))
                )
              )
            )
          )
        )
      )
      (.zeroFace 12 0
        (.retain 37)
      )
    )
    (.zeroFace 12 2
      (.retain 35)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 2 0) (i6D1006LeafValid 2 2 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 2 0) root = (18775468381 / 20000000000000) := by
  decide +kernel

end C082S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
