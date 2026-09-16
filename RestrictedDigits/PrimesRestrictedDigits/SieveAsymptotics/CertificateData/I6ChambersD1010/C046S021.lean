import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S021
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S021

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(309993 / 4000000), (309993 / 4000000), (309993 / 4000000)],
    ![(180001 / 2000000), (16249 / 250000), (16249 / 250000)],
    ![(180001 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(180001 / 2000000), (180001 / 2000000), (180001 / 2000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 5 (1 / 2)
      (.split 2 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (396359485870080000 / 125067512150729))
              (.retain (394416094617600000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (344497053573120000 / 125067512150729))
              (.retain (376641578065920000 / 125067512150729))
            )
          )
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (329751320801280000 / 125067512150729))
              (.retain (363496872099840000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (349133224796160000 / 125067512150729))
              (.retain (370470881402880000 / 125067512150729))
            )
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (348166946426880000 / 125067512150729))
              (.retain (312706652958720000 / 125067512150729))
            )
            (.split 4 (1 / 2)
              (.retain (354604493475840000 / 125067512150729))
              (.retain (330426498478080000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (368515028275200000 / 125067512150729))
              (.retain (343127421603840000 / 125067512150729))
            )
            (.split 2 (1 / 2)
              (.retain (375451707187200000 / 125067512150729))
              (.retain (363211442503680000 / 125067512150729))
            )
          )
        )
      )
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (208804582625280000 / 125067512150729))
            (.retain (136401386680320000 / 125067512150729))
          )
          (.split 4 (1 / 2)
            (.retain (244639609466880000 / 125067512150729))
            (.retain (253644379514880000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (279067557795840000 / 125067512150729))
            (.split 3 (1 / 2)
              (.retain (273818719764480000 / 125067512150729))
              (.retain (303610458869760000 / 125067512150729))
            )
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (284100419420160000 / 125067512150729))
              (.retain (315101770260480000 / 125067512150729))
            )
            (.split 1 (1 / 2)
              (.retain (289534925045760000 / 125067512150729))
              (.retain (333633806868480000 / 125067512150729))
            )
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (224674422712320000 / 125067512150729))
            (.retain (146529306501120000 / 125067512150729))
          )
          (.retain (98094940139520000 / 125067512150729))
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (233261519155200000 / 125067512150729))
            (.retain (152254037483520000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.retain (273339552491520000 / 125067512150729))
            (.split 1 (1 / 2)
              (.retain (260329688924160000 / 125067512150729))
              (.retain (306797207347200000 / 125067512150729))
            )
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (5675642787840000 / 2908546794203))
            (.retain (159448117954560000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (113006074091520000 / 125067512150729))
            (.retain (117437887426560000 / 125067512150729))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (243299219804160000 / 125067512150729))
            (.retain (158945837905920000 / 125067512150729))
          )
          (.split 2 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (296142947942400000 / 125067512150729))
              (.retain (271603544985600000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (276758417817600000 / 125067512150729))
              (.retain (313145268080640000 / 125067512150729))
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (260669692399 / 100000000000000) := by
  decide +kernel

end C046S021
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
