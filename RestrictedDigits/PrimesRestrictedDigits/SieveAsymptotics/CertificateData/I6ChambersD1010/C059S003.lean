import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S003

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(38701 / 240000), (180001 / 1500000), (472483 / 6000000)],
    ![(802511 / 6000000), (802511 / 6000000), (55499 / 600000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (1 / 2)
    (.split 4 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1182425180037120000 / 561658568377843))
              (.retain (1133341168435200000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (1096859040768000000 / 561658568377843))
              (.retain (1074432246865920000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (1045483517583360000 / 561658568377843))
              (.retain (1021191794565120000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (989921451294720000 / 561658568377843))
              (.retain (921761810841600000 / 561658568377843))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (975429319680000000 / 561658568377843))
              (.retain (913974637363200000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (990504684011520000 / 561658568377843))
              (.retain (961628776243200000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (991571236208640000 / 561658568377843))
              (.retain (964054201835520000 / 561658568377843))
            )
            (.retain (897022339706880000 / 561658568377843))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (885583323832320000 / 561658568377843))
              (.retain (849934310768640000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (869923315261440000 / 561658568377843))
              (.retain (799398593003520000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (888691526369280000 / 561658568377843))
              (.retain (854639475056640000 / 561658568377843))
            )
            (.retain (851219369164800000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (857340511395840000 / 561658568377843))
              (.retain (784158129192960000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (726970875863040000 / 561658568377843))
              (.retain (689020371394560000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (843462174965760000 / 561658568377843))
              (.retain (771740670689280000 / 561658568377843))
            )
            (.retain (821903525498880000 / 561658568377843))
          )
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (772929689518080000 / 561658568377843))
              (.retain (792170675159040000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (785244219678720000 / 561658568377843))
              (.retain (749664919388160000 / 561658568377843))
            )
          )
          (.split 4 (1 / 2)
            (.retain (691554904289280000 / 561658568377843))
            (.retain (670678344990720000 / 561658568377843))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (693667641692160000 / 561658568377843))
            (.retain (672654776832000000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (632732980101120000 / 561658568377843))
            (.retain (610184457768960000 / 561658568377843))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (656704218378240000 / 561658568377843))
            (.retain (575259003371520000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (541171574046720000 / 561658568377843))
            (.retain (561841052958720000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (432047669575680000 / 561658568377843))
            (.retain (448959061463040000 / 561658568377843))
          )
          (.retain (324974462146560000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (65102202061 / 50000000000000) := by
  decide +kernel

end C059S003
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
