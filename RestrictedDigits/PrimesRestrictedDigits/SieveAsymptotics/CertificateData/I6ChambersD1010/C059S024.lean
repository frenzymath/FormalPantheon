import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S024
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S024

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(802511 / 6000000), (802511 / 6000000), (55499 / 600000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 2 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (1173979748597760000 / 561658568377843))
                (.retain (1114479340830720000 / 561658568377843))
              )
              (.retain (1096726907473920000 / 561658568377843))
            )
            (.retain (975664221050880000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (970284744253440000 / 561658568377843))
              (.retain (893676954009600000 / 561658568377843))
            )
            (.retain (910817035776000000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (969980351938560000 / 561658568377843))
                (.retain (899355972280320000 / 561658568377843))
              )
              (.retain (874911818280960000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (958139076280320000 / 561658568377843))
                (.retain (888461998571520000 / 561658568377843))
              )
              (.retain (842650377154560000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (902155064647680000 / 561658568377843))
              (.retain (822128485109760000 / 561658568377843))
            )
            (.retain (842745426094080000 / 561658568377843))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (708426119761920000 / 561658568377843))
              (.retain (633531290480640000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (687862165708800000 / 561658568377843))
              (.retain (689009977589760000 / 561658568377843))
            )
          )
          (.split 3 (1 / 2)
            (.retain (725035563048960000 / 561658568377843))
            (.split 4 (1 / 2)
              (.retain (705452358942720000 / 561658568377843))
              (.retain (706600170639360000 / 561658568377843))
            )
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (619024117248000000 / 561658568377843))
              (.retain (540977527664640000 / 561658568377843))
            )
            (.retain (612409002762240000 / 561658568377843))
          )
          (.split 5 (1 / 2)
            (.retain (357778926950400000 / 561658568377843))
            (.retain (475065330094080000 / 561658568377843))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (698792419491840000 / 561658568377843))
              (.retain (716473325076480000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (652717442949120000 / 561658568377843))
              (.retain (571822295040000000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (589247146045440000 / 561658568377843))
              (.retain (507465115914240000 / 561658568377843))
            )
            (.retain (346551432192000000 / 561658568377843))
          )
        )
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (591050609049600000 / 561658568377843))
              (.retain (508991123128320000 / 561658568377843))
            )
            (.retain (347661255536640000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (248629358131200000 / 561658568377843))
            (.retain (241438839091200000 / 561658568377843))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (667510684139520000 / 561658568377843))
              (.retain (584311469322240000 / 561658568377843))
            )
            (.retain (643651134566400000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (570105412853760000 / 561658568377843))
              (.retain (483159743447040000 / 561658568377843))
            )
            (.retain (331625799106560000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (541333413457920000 / 561658568377843))
            (.retain (323358450278400000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (223308639682560000 / 561658568377843))
            (.retain (218158209423360000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (104621655773 / 50000000000000) := by
  decide +kernel

end C059S024
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
