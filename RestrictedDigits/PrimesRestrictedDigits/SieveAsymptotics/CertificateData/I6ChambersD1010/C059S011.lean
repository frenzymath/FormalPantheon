import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C059S011
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C059S011

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(691513 / 4800000), (2467481 / 24000000), (2467481 / 24000000)],
    ![(65627 / 375000), (55499 / 600000), (55499 / 600000)],
    ![(1262531 / 8000000), (932503 / 8000000), (24099 / 320000)],
    ![(147503 / 1000000), (212499 / 2000000), (212499 / 2000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (3 / 4));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 5 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (982129642536960000 / 561658568377843))
              (.retain (863986024488960000 / 561658568377843))
            )
            (.split 1 (1 / 2)
              (.retain (822325785845760000 / 561658568377843))
              (.retain (863041045340160000 / 561658568377843))
            )
          )
          (.split 0 (1 / 2)
            (.retain (688017726074880000 / 561658568377843))
            (.split 1 (1 / 2)
              (.retain (742709428715520000 / 561658568377843))
              (.retain (786209155153920000 / 561658568377843))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (369618199142400000 / 561658568377843))
            (.retain (485378173071360000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (586488336629760000 / 561658568377843))
            (.retain (670177994526720000 / 561658568377843))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (1027971159367680000 / 561658568377843))
              (.retain (1005730595020800000 / 561658568377843))
            )
            (.retain (938968972369920000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (723175585136640000 / 561658568377843))
              (.retain (800113566597120000 / 561658568377843))
            )
            (.retain (893165647196160000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (882433275494400000 / 561658568377843))
              (.retain (744040157921280000 / 561658568377843))
            )
            (.split 4 (1 / 2)
              (.retain (935302481510400000 / 561658568377843))
              (.retain (908725574983680000 / 561658568377843))
            )
          )
          (.split 5 (1 / 2)
            (.retain (902037816668160000 / 561658568377843))
            (.split 1 (1 / 2)
              (.retain (730316599418880000 / 561658568377843))
              (.retain (808120158658560000 / 561658568377843))
            )
          )
        )
      )
    )
    (.split 5 (1 / 2)
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (959022076538880000 / 561658568377843))
            (.retain (843828360744960000 / 561658568377843))
          )
          (.split 3 (1 / 2)
            (.retain (803151422668800000 / 561658568377843))
            (.retain (842883381596160000 / 561658568377843))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (888346973675520000 / 561658568377843))
            (.retain (770291015086080000 / 561658568377843))
          )
          (.retain (843482733742080000 / 561658568377843))
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (489709885132800000 / 561658568377843))
            (.retain (333279765319680000 / 561658568377843))
          )
          (.split 0 (1 / 2)
            (.retain (658789116088320000 / 561658568377843))
            (.retain (556625538109440000 / 561658568377843))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (637571526819840000 / 561658568377843))
            (.split 4 (1 / 2)
              (.retain (712973900759040000 / 561658568377843))
              (.retain (754731067760640000 / 561658568377843))
            )
          )
          (.split 2 (1 / 2)
            (.retain (654309492940800000 / 561658568377843))
            (.retain (675144818380800000 / 561658568377843))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 5 0) (i6D1006LeafValid 2 5 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 5 0) root = (6478078697 / 5000000000000) := by
  decide +kernel

end C059S011
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
