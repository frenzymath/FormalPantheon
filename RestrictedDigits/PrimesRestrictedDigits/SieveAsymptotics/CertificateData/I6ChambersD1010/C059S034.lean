import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S034
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S034

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(212499 / 2000000), (212499 / 2000000), (212499 / 2000000)],
    ![(1097517 / 8000000), (767489 / 8000000), (767489 / 8000000)],
    ![(101501 / 800000), (101501 / 800000), (342491 / 4000000)],
    ![(180001 / 1500000), (180001 / 1500000), (180001 / 1500000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.split 2 (1 / 2)
                (.retain (1065682492231680000 / 561658568377843))
                (.retain (907832248934400000 / 561658568377843))
              )
              (.split 3 (1 / 2)
                (.retain (813325687050240000 / 561658568377843))
                (.retain (876998664253440000 / 561658568377843))
              )
            )
            (.split 3 (1 / 2)
              (.split 5 (1 / 2)
                (.retain (797686046392320000 / 561658568377843))
                (.retain (731940226007040000 / 561658568377843))
              )
              (.split 0 (1 / 2)
                (.retain (752538380267520000 / 561658568377843))
                (.retain (751138834083840000 / 561658568377843))
              )
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (604901975777280000 / 561658568377843))
              (.split 4 (1 / 2)
                (.retain (592937723105280000 / 561658568377843))
                (.retain (594082806497280000 / 561658568377843))
              )
            )
            (.split 2 (1 / 2)
              (.retain (518234741729280000 / 561658568377843))
              (.retain (353068408903680000 / 561658568377843))
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (377242373836800000 / 561658568377843))
              (.retain (196929658091520000 / 561658568377843))
            )
            (.retain (278040024115200000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (533636423608320000 / 561658568377843))
              (.split 3 (1 / 2)
                (.retain (486528504791040000 / 561658568377843))
                (.retain (559548707328000000 / 561658568377843))
              )
            )
            (.split 2 (1 / 2)
              (.retain (448886975201280000 / 561658568377843))
              (.retain (269904977694720000 / 561658568377843))
            )
          )
        )
      )
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.split 2 (1 / 2)
                (.retain (1046187451514880000 / 561658568377843))
                (.retain (876928887336960000 / 561658568377843))
              )
              (.split 0 (1 / 2)
                (.retain (852595919400960000 / 561658568377843))
                (.retain (762876165427200000 / 561658568377843))
              )
            )
            (.split 0 (1 / 2)
              (.split 3 (1 / 2)
                (.retain (737886587166720000 / 561658568377843))
                (.retain (739286133350400000 / 561658568377843))
              )
              (.retain (725823529390080000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (563462591109120000 / 561658568377843))
              (.split 3 (1 / 2)
                (.retain (573332365578240000 / 561658568377843))
                (.retain (574477448970240000 / 561658568377843))
              )
            )
            (.split 1 (1 / 2)
              (.retain (483486409728000000 / 561658568377843))
              (.retain (319270594129920000 / 561658568377843))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (300971205181440000 / 561658568377843))
              (.retain (377334760089600000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (500165785405440000 / 561658568377843))
              (.retain (501183637217280000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (213874270617600000 / 561658568377843))
              (.retain (291946978437120000 / 561658568377843))
            )
            (.split 2 (1 / 2)
              (.retain (329264825149440000 / 561658568377843))
              (.retain (163163918960640000 / 561658568377843))
            )
          )
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (441049890723840000 / 561658568377843))
              (.retain (275354764922880000 / 561658568377843))
            )
            (.split 0 (1 / 2)
              (.retain (185276280545280000 / 561658568377843))
              (.retain (181998292746240000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.retain (98390087930880000 / 561658568377843))
            (.retain (94988439152640000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (351551953244160000 / 561658568377843))
              (.retain (182972999669760000 / 561658568377843))
            )
            (.retain (91964385653760000 / 561658568377843))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (350195734056960000 / 561658568377843))
              (.retain (182159268157440000 / 561658568377843))
            )
            (.retain (90834615521280000 / 561658568377843))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (259140697159680000 / 561658568377843))
            (.retain (88172473282560000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.retain (260225672509440000 / 561658568377843))
            (.retain (89302243415040000 / 561658568377843))
          )
        )
        (.split 2 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (336263232568320000 / 561658568377843))
            (.split 3 (1 / 2)
              (.retain (171863025868800000 / 561658568377843))
              (.retain (169816729190400000 / 561658568377843))
            )
          )
          (.split 1 (1 / 2)
            (.retain (84668401658880000 / 561658568377843))
            (.retain (82597293158400000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (236773803727 / 100000000000000) := by
  decide +kernel

end C059S034
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
