import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C102S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C102S001

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(55499 / 300000), (180001 / 1500000), (180001 / 1500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(212499 / 1000000), (147503 / 1000000), (16249 / 250000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (32498 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (82507 / 115005)
    (.zeroFace 1 0
      (.split 3 (1 / 2)
        (.zeroFace 9 0
          (.retain 0)
        )
        (.retain 0)
      )
    )
    (.split 4 (2 / 3)
      (.split 5 (1 / 2)
        (.split 0 (45005 / 82507)
          (.split 3 (75004 / 82507)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.split 2 (1 / 2)
                  (.retain (368736477840000 / 3869268981257))
                  (.retain (869666365440000 / 3869268981257))
                )
                (.split 1 (1 / 2)
                  (.retain (388988002800000 / 3869268981257))
                  (.retain (879479920080000 / 3869268981257))
                )
              )
              (.split 1 (1 / 2)
                (.retain (313414224480000 / 3869268981257))
                (.split 2 (1 / 2)
                  (.retain (572864954400000 / 3869268981257))
                  (.split 0 (1 / 2)
                    (.retain (822206244960000 / 3869268981257))
                    (.retain (1241912034720000 / 3869268981257))
                  )
                )
              )
            )
            (.split 4 (75004 / 82507)
              (.split 5 (1 / 2)
                (.split 2 (1 / 2)
                  (.retain (117287187570000 / 879351602501))
                  (.split 0 (1 / 2)
                    (.retain (192096851580000 / 879351602501))
                    (.split 1 (1 / 2)
                      (.retain (220664809800000 / 879351602501))
                      (.retain (326072625120000 / 879351602501))
                    )
                  )
                )
                (.split 3 (1 / 2)
                  (.split 1 (1 / 2)
                    (.retain (114473687580000 / 879351602501))
                    (.retain (214282420740000 / 879351602501))
                  )
                  (.split 0 (1 / 2)
                    (.retain (142382032380000 / 879351602501))
                    (.retain (5568621300000 / 21447600061))
                  )
                )
              )
              (.zeroFace 15 0
                (.retain 330)
              )
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.split 2 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (5312967182208000 / 61273452846049))
                    (.retain (4874579457408000 / 61273452846049))
                  )
                  (.split 1 (1 / 2)
                    (.retain (4678841905920000 / 61273452846049))
                    (.retain (4641830572032000 / 61273452846049))
                  )
                )
                (.split 3 (1 / 2)
                  (.split 1 (1 / 2)
                    (.retain (8796547002240000 / 61273452846049))
                    (.retain (8722524337920000 / 61273452846049))
                  )
                  (.split 0 (1 / 2)
                    (.split 4 (1 / 2)
                      (.retain (19169884707840000 / 61273452846049))
                      (.retain (22245821496576000 / 61273452846049))
                    )
                    (.split 1 (1 / 2)
                      (.retain (14859678458880000 / 61273452846049))
                      (.retain (10747359866880000 / 61273452846049))
                    )
                  )
                )
              )
              (.split 1 (1 / 2)
                (.split 3 (1 / 2)
                  (.retain (3781696768128000 / 61273452846049))
                  (.split 4 (1 / 2)
                    (.retain (7903458855936000 / 61273452846049))
                    (.split 0 (1 / 2)
                      (.retain (19207134913536000 / 61273452846049))
                      (.retain (11455407279360000 / 61273452846049))
                    )
                  )
                )
                (.split 4 (1 / 2)
                  (.retain (4127686727616000 / 61273452846049))
                  (.split 0 (1 / 2)
                    (.split 3 (1 / 2)
                      (.retain (11778916831488000 / 61273452846049))
                      (.retain (19692399241728000 / 61273452846049))
                    )
                    (.retain (8072068352256000 / 61273452846049))
                  )
                )
              )
            )
            (.split 1 (1 / 2)
              (.split 5 (1 / 2)
                (.split 4 (1 / 2)
                  (.retain (3890517018624000 / 61273452846049))
                  (.split 3 (1 / 2)
                    (.retain (7550493162624000 / 61273452846049))
                    (.split 0 (1 / 2)
                      (.retain (19104466823424000 / 61273452846049))
                      (.retain (11138099298048000 / 61273452846049))
                    )
                  )
                )
                (.split 3 (1 / 2)
                  (.retain (3566031816960000 / 61273452846049))
                  (.split 4 (1 / 2)
                    (.retain (7307860998528000 / 61273452846049))
                    (.split 0 (1 / 2)
                      (.retain (18619202495232000 / 61273452846049))
                      (.retain (10814589745920000 / 61273452846049))
                    )
                  )
                )
              )
              (.split 0 (1 / 2)
                (.split 4 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (7755760240128000 / 61273452846049))
                    (.retain (7398453005568000 / 61273452846049))
                  )
                  (.split 3 (1 / 2)
                    (.retain (10959711239808000 / 61273452846049))
                    (.split 0 (1 / 2)
                      (.retain (20889541391616000 / 61273452846049))
                      (.retain (16741122107904000 / 61273452846049))
                    )
                  )
                )
                (.split 2 (1 / 2)
                  (.retain (3700260202752000 / 61273452846049))
                  (.retain (3523752291456000 / 61273452846049))
                )
              )
            )
          )
        )
        (.zeroFace 9 0
          (.split 0 (45005 / 82507)
            (.split 3 (37502 / 82507)
              (.retain 242)
              (.split 4 (75004 / 82507)
                (.retain 263)
                (.zeroFace 15 0
                  (.retain 393)
                )
              )
            )
            (.retain 118)
          )
        )
      )
      (.zeroFace 9 0
        (.split 2 (45005 / 82507)
          (.split 4 (45005 / 82507)
            (.split 5 (45005 / 82507)
              (.zeroFace 15 0
                (.retain 507)
              )
              (.retain 371)
            )
            (.retain 241)
          )
          (.retain 117)
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 4) (i6D1006LeafValid 2 3 4) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 4) root = (87384961833 / 100000000000000) := by
  decide +kernel

end C102S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
