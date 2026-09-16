import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S017
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S017

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(672519 / 4000000), (342491 / 4000000), (342491 / 4000000)],
    ![(377513 / 2000000), (212499 / 2000000), (16249 / 250000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).1 (T.edgePointD1000 3 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (704970887823360000 / 561658568377843))
              (.retain (584297944657920000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (466478578298880000 / 561658568377843))
              (.retain (345500156805120000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.retain (286054059386880000 / 561658568377843))
            (.retain (280269028823040000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.retain (139744906859520000 / 561658568377843))
          (.retain (141813129507840000 / 561658568377843))
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (719427154452480000 / 561658568377843))
              (.retain (621705090355200000 / 561658568377843))
            )
            (.retain (424982935848960000 / 561658568377843))
          )
          (.split 1 (1 / 2)
            (.retain (299699182909440000 / 561658568377843))
            (.retain (293914152345600000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (166128172784640000 / 561658568377843))
          (.retain (156356540605440000 / 561658568377843))
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (685649873018880000 / 561658568377843))
              (.retain (567949393797120000 / 561658568377843))
            )
            (.split 3 (1 / 2)
              (.retain (453102491197440000 / 561658568377843))
              (.retain (335096533647360000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.retain (264065063086080000 / 561658568377843))
            (.retain (255232099031040000 / 561658568377843))
          )
        )
        (.split 3 (1 / 2)
          (.retain (132435909550080000 / 561658568377843))
          (.retain (134504132198400000 / 561658568377843))
        )
      )
      (.split 5 (1 / 2)
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (506634153246720000 / 561658568377843))
            (.retain (265798196490240000 / 561658568377843))
          )
          (.split 4 (1 / 2)
            (.retain (489748041584640000 / 561658568377843))
            (.retain (250226808791040000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.retain (130780533611520000 / 561658568377843))
          (.retain (125091691637760000 / 561658568377843))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (46725384153 / 50000000000000) := by
  decide +kernel

end C059S017
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
