import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C046S014
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C046S014

abbrev label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(23001 / 200000), (16249 / 250000), (16249 / 250000)],
    ![(82507 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(280019 / 2000000), (180001 / 2000000), (16249 / 250000)],
    ![(510029 / 4000000), (309993 / 4000000), (309993 / 4000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (82507 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (165014 / 345015));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).2 (T.edgePointD1000 1 (50009 / 82507));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (150027 / 330028));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 4 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (165821277327360000 / 125067512150729))
              (.retain (111948136335360000 / 125067512150729))
            )
            (.split 3 (1 / 2)
              (.retain (110652074803200000 / 125067512150729))
              (.retain (112666665646080000 / 125067512150729))
            )
          )
          (.split 3 (1 / 2)
            (.retain (48272685957120000 / 125067512150729))
            (.split 4 (1 / 2)
              (.retain (79990511585280000 / 125067512150729))
              (.retain (81557415567360000 / 125067512150729))
            )
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (172629863454720000 / 125067512150729))
              (.retain (116661772892160000 / 125067512150729))
            )
            (.split 0 (1 / 2)
              (.retain (115099873751040000 / 125067512150729))
              (.retain (117798919495680000 / 125067512150729))
            )
          )
          (.split 1 (1 / 2)
            (.retain (71221513036800000 / 125067512150729))
            (.retain (74070358410240000 / 125067512150729))
          )
        )
      )
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (50024353858560000 / 125067512150729))
            (.retain (16628376084480000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (34747994373120000 / 125067512150729))
            (.retain (36779463905280000 / 125067512150729))
          )
        )
        (.split 0 (1 / 2)
          (.split 4 (1 / 2)
            (.retain (52196614410240000 / 125067512150729))
            (.retain (18096930938880000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (35448602234880000 / 125067512150729))
            (.retain (37480071767040000 / 125067512150729))
          )
        )
      )
    )
    (.split 1 (1 / 2)
      (.split 3 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (155158366371840000 / 125067512150729))
              (.retain (101142340300800000 / 125067512150729))
            )
            (.retain (68333238773760000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (32893044433920000 / 125067512150729))
            (.retain (34647815424000000 / 125067512150729))
          )
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (161443215114240000 / 125067512150729))
              (.retain (2449586964480000 / 2908546794203))
            )
            (.retain (71475663144960000 / 125067512150729))
          )
          (.split 0 (1 / 2)
            (.retain (38699747481600000 / 125067512150729))
            (.retain (38001415096320000 / 125067512150729))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 4 (1 / 2)
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (166903120865280000 / 125067512150729))
              (.retain (108972176640000000 / 125067512150729))
            )
            (.retain (78785974932480000 / 125067512150729))
          )
          (.split 3 (1 / 2)
            (.retain (40291594552320000 / 125067512150729))
            (.retain (40989926937600000 / 125067512150729))
          )
        )
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (171243950284800000 / 125067512150729))
              (.retain (111866062909440000 / 125067512150729))
            )
            (.retain (80956389642240000 / 125067512150729))
          )
          (.split 1 (1 / 2)
            (.retain (42607864151040000 / 125067512150729))
            (.retain (45225943772160000 / 125067512150729))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 0 0) (i6D1006LeafValid 2 0 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 0 0) root = (144617159813 / 100000000000000) := by
  decide +kernel

end C046S014
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
