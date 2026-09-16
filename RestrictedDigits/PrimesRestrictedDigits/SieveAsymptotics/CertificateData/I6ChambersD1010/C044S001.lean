import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C044S001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C044S001

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(319999 / 2000000), (319999 / 2000000), (319999 / 2000000)],
    ![(55001 / 250000), (69999 / 500000), (69999 / 500000)],
    ![(180001 / 1000000), (180001 / 1000000), (69999 / 500000)],
    ![(194999 / 1125000), (194999 / 1125000), (194999 / 1125000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (75002 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (75002 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (239993 / 360027));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (75002 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (75002 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (239993 / 360027));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (36667 / 40003)
    (.split 3 (5004 / 40003)
      (.split 2 (115005 / 174997)
        (.split 4 (120009 / 180001)
          (.split 5 (120009 / 180001)
            (.zeroFace 10 0
              (.retain 196)
            )
            (.retain (397444406807128638207560625 / 2626444814177388811642919))
          )
          (.split 3 (1 / 2)
            (.retain (36392801212284328770000 / 350239340469047714581))
            (.retain (36702722656059962100000 / 350239340469047714581))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (474892728992226000 / 8951472336654991))
            (.retain (478824728885358000 / 8951472336654991))
          )
          (.split 2 (1 / 2)
            (.retain (710118262385382000 / 8951472336654991))
            (.retain (246908334513132000 / 8951472336654991))
          )
        )
      )
      (.split 4 (11259 / 105011)
        (.split 2 (115005 / 174997)
          (.split 4 (1321954230 / 2109431719)
            (.split 5 (120009 / 180001)
              (.zeroFace 10 0
                (.retain 196)
              )
              (.retain (102061627563929212958188125 / 667586304377897964752576))
            )
            (.retain (197316132568740870246375 / 1735634279331250160512))
          )
          (.retain (628515217623343116875 / 9998973890369291256))
        )
        (.zeroFace 6 0
          (.retain 10)
        )
      )
    )
    (.split 2 (120009 / 239993)
      (.split 4 (115005 / 174997)
        (.split 5 (120009 / 180001)
          (.zeroFace 10 0
            (.retain 168)
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (319826721367608731173125 / 3299644941732519115003))
              (.split 0 (1 / 2)
                (.retain (521804336721647879283750 / 3299644941732519115003))
                (.retain (424684970125953206197500 / 3299644941732519115003))
              )
            )
            (.split 0 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (476162239135247889840000 / 3299644941732519115003))
                (.retain (570970612447774091325000 / 3299644941732519115003))
              )
              (.retain (479565028056887951574375 / 3299644941732519115003))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (7377549301658124000 / 84332846153564833))
                (.retain (3123307316170980000 / 84332846153564833))
              )
              (.split 4 (1 / 2)
                (.retain (8853742376457300000 / 84332846153564833))
                (.retain (4740601919645340000 / 84332846153564833))
              )
            )
            (.split 4 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (10161924670990656000 / 84332846153564833))
                (.retain (6098940999633348000 / 84332846153564833))
              )
              (.split 0 (1 / 2)
                (.retain (77147047356516000 / 2056898686672313))
                (.retain (4768051689369792000 / 84332846153564833))
              )
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (12682104688764000 / 120994040392489))
                (.retain (4730005652498748000 / 84332846153564833))
              )
              (.split 0 (1 / 2)
                (.retain (8278603249154220000 / 84332846153564833))
                (.retain (8270250405048288000 / 84332846153564833))
              )
            )
            (.split 0 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (9666463830950664000 / 84332846153564833))
                (.retain (9676179631491228000 / 84332846153564833))
              )
              (.split 2 (1 / 2)
                (.retain (105996199491144000 / 773695836271237))
                (.retain (10437790748876820000 / 84332846153564833))
              )
            )
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (5897539958400000 / 58676000410003))
                (.retain (133579520640000 / 1585837848919))
              )
              (.retain (3345950681280000 / 58676000410003))
            )
            (.split 1 (1 / 2)
              (.retain (2322884142720000 / 58676000410003))
              (.retain (2280996089280000 / 58676000410003))
            )
          )
          (.split 3 (1 / 2)
            (.retain (1178852919840000 / 58676000410003))
            (.retain (1185499008000000 / 58676000410003))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (4340828787840000 / 58676000410003))
              (.retain (2231342559360000 / 58676000410003))
            )
            (.retain (1154369769120000 / 58676000410003))
          )
          (.split 4 (1 / 2)
            (.retain (3205599042240000 / 58676000410003))
            (.retain (1098410394240000 / 58676000410003))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 0) (i6D1006LeafValid 1 6 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0) root = (11419526931 / 25000000000000) := by
  decide +kernel

end C044S001
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
