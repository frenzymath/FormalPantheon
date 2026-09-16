import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S006

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(147503 / 1000000), (212499 / 2000000), (212499 / 2000000)],
    ![(38701 / 240000), (180001 / 1500000), (472483 / 6000000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 2 (1 / 2)
    (.split 5 (1 / 2)
      (.split 4 (1 / 2)
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (1194905817538560000 / 561658568377843))
              (.retain (1172147924090880000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (1088507567923200000 / 561658568377843))
              (.retain (1137238749757440000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (1050714727096320000 / 561658568377843))
              (.retain (1101434231070720000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (1004919215800320000 / 561658568377843))
              (.retain (937941688811520000 / 561658568377843))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1095365933752320000 / 561658568377843))
              (.retain (1040544291225600000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (1110952294686720000 / 561658568377843))
              (.retain (1088933503057920000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1080050276966400000 / 561658568377843))
              (.retain (1026284886466560000 / 561658568377843))
            )
            (.retain (946020961013760000 / 561658568377843))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (876326458613760000 / 561658568377843))
              (.retain (844382829404160000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (712052123074560000 / 561658568377843))
              (.retain (791179282391040000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (880428735774720000 / 561658568377843))
              (.retain (850220774645760000 / 561658568377843))
            )
            (.retain (840121316904960000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (988460406374400000 / 561658568377843))
              (.retain (963934513643520000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (1017190925107200000 / 561658568377843))
              (.retain (1050883252346880000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (943483952332800000 / 561658568377843))
              (.retain (917538652938240000 / 561658568377843))
            )
            (.retain (902785240350720000 / 561658568377843))
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (768945307852800000 / 561658568377843))
              (.retain (735853882982400000 / 561658568377843))
            )
            (.retain (776739359416320000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (659674835066880000 / 561658568377843))
              (.retain (742932312145920000 / 561658568377843))
            )
            (.retain (722025606942720000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (880163618365440000 / 561658568377843))
              (.retain (908262307676160000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (954236516474880000 / 561658568377843))
              (.retain (1013058263162880000 / 561658568377843))
            )
          )
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (820943167979520000 / 561658568377843))
              (.retain (791025595269120000 / 561658568377843))
            )
            (.retain (832354400378880000 / 561658568377843))
          )
        )
      )
      (.split 2 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (677251631001600000 / 561658568377843))
            (.retain (640836246343680000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (586158526218240000 / 561658568377843))
            (.retain (610552703324160000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (501139588239360000 / 561658568377843))
            (.retain (530552530022400000 / 561658568377843))
          )
          (.retain (353271913758720000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (5727786751 / 4000000000000) := by
  decide +kernel

end C059S006
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
