import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S005
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S005

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(43 / 200), (180001 / 1500000), (180001 / 1500000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(101501 / 400000), (212499 / 2000000), (342491 / 4000000)],
    ![(126251 / 500000), (43 / 400), (43 / 400)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (63756 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (758 / 24395));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (9546 / 17425));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (239993 / 817542));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (412535 / 472527));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (340381137 / 650072653));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (63756 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 4 (1 / 2)
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (2666757137760000 / 2739894188647))
              (.split 3 (1 / 2)
                (.retain (2440471893120000 / 2739894188647))
                (.retain (401004437760000 / 391413455521))
              )
            )
            (.split 1 (1 / 2)
              (.retain (2228331110400000 / 2739894188647))
              (.retain (2186696223840000 / 2739894188647))
            )
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (1004169584160000 / 2739894188647))
              (.retain (1371722700000000 / 2739894188647))
            )
            (.split 2 (1 / 2)
              (.retain (284138899200000 / 391413455521))
              (.retain (1933513061280000 / 2739894188647))
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (1841299239840000 / 2739894188647))
            (.retain (1025522869680000 / 2739894188647))
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (2390199612480000 / 2739894188647))
              (.retain (2279982005760000 / 2739894188647))
            )
            (.split 1 (1 / 2)
              (.retain (178063742400000 / 249081289877))
              (.retain (2026825601280000 / 2739894188647))
            )
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (1499343640320000 / 2739894188647))
              (.retain (1200405752160000 / 2739894188647))
            )
            (.retain (666600420960000 / 2739894188647))
          )
          (.split 0 (1 / 2)
            (.retain (135676708560000 / 391413455521))
            (.split 2 (1 / 2)
              (.retain (1441469492640000 / 2739894188647))
              (.retain (1144364045760000 / 2739894188647))
            )
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (100015899840000 / 161170246391))
              (.retain (204676836000000 / 391413455521))
            )
            (.split 3 (1 / 2)
              (.retain (814229704800000 / 2739894188647))
              (.split 0 (1 / 2)
                (.retain (797580148800000 / 2739894188647))
                (.retain (1055218529280000 / 2739894188647))
              )
            )
          )
          (.split 0 (1 / 2)
            (.split 0 (1 / 2)
              (.retain (1401298972320000 / 2739894188647))
              (.retain (1445476736160000 / 2739894188647))
            )
            (.split 1 (1 / 2)
              (.retain (1333137713280000 / 2739894188647))
              (.split 2 (1 / 2)
                (.retain (1809969906240000 / 2739894188647))
                (.retain (1489833606720000 / 2739894188647))
              )
            )
          )
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 0 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (9717684000000 / 10829621299))
              (.retain (2011760619840000 / 2739894188647))
            )
            (.split 3 (1 / 2)
              (.retain (165961957920000 / 249081289877))
              (.retain (1778631525600000 / 2739894188647))
            )
          )
          (.split 1 (1 / 2)
            (.retain (59626767840000 / 161170246391))
            (.split 4 (1 / 2)
              (.retain (202033894080000 / 391413455521))
              (.retain (1350589320000000 / 2739894188647))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (2131254358560000 / 2739894188647))
              (.retain (1527348559200000 / 2739894188647))
            )
            (.split 3 (1 / 2)
              (.retain (868598886240000 / 2739894188647))
              (.retain (1221394522560000 / 2739894188647))
            )
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (2264441011680000 / 2739894188647))
              (.retain (239837774400000 / 391413455521))
            )
            (.split 0 (1 / 2)
              (.retain (1545276289440000 / 2739894188647))
              (.retain (219730967520000 / 391413455521))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (1592312973600000 / 2739894188647))
              (.retain (806134651200000 / 2739894188647))
            )
            (.split 2 (1 / 2)
              (.retain (1659967751040000 / 2739894188647))
              (.retain (156995802720000 / 391413455521))
            )
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (189549779040000 / 249081289877))
              (.retain (1658138353440000 / 2739894188647))
            )
            (.retain (1319447011920000 / 2739894188647))
          )
        )
        (.split 2 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (2505220793280000 / 2739894188647))
                (.retain (296320260480000 / 391413455521))
              )
              (.retain (1734810825600000 / 2739894188647))
            )
            (.retain (1782910977600000 / 2739894188647))
          )
          (.split 0 (1 / 2)
            (.split 0 (1 / 2)
              (.retain (1506116148480000 / 2739894188647))
              (.retain (1494962484480000 / 2739894188647))
            )
            (.split 1 (1 / 2)
              (.retain (204181907040000 / 391413455521))
              (.split 2 (1 / 2)
                (.retain (1608378036480000 / 2739894188647))
                (.retain (205550524800000 / 391413455521))
              )
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (26130404523 / 12500000000000) := by
  decide +kernel

end C100S005
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
