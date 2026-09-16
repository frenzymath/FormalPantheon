import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S009
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S009

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(398470879 / 1651600000), (55499 / 600000), (55499 / 600000)],
    ![(147503 / 500000), (16249 / 250000), (16249 / 250000)],
    ![(101501 / 400000), (212499 / 2000000), (342491 / 4000000)],
    ![(43 / 200), (180001 / 1500000), (180001 / 1500000)]
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (340381137 / 650072653));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).2 (T.edgePointD1000 2 (340381137 / 650072653));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).1 (T.edgePointD1000 0 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (1 / 2)
    (.split 4 (1 / 2)
      (.split 5 (1 / 2)
        (.split 2 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (358888105622937600000 / 772370756866053571))
              (.retain (325343755223930880000 / 772370756866053571))
            )
            (.retain (342574337769500160000 / 772370756866053571))
          )
          (.split 1 (1 / 2)
            (.retain (284958180358064640000 / 772370756866053571))
            (.split 2 (1 / 2)
              (.retain (264489273780940800000 / 772370756866053571))
              (.retain (211479120647009280000 / 772370756866053571))
            )
          )
        )
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (212070224323169280000 / 772370756866053571))
              (.retain (154806913615288320000 / 772370756866053571))
            )
            (.retain (115169986705075200000 / 772370756866053571))
          )
          (.split 2 (1 / 2)
            (.retain (278244438217873920000 / 772370756866053571))
            (.retain (228309949865157120000 / 772370756866053571))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (336481607239326720000 / 772370756866053571))
            (.retain (242416644947343360000 / 772370756866053571))
          )
          (.split 1 (1 / 2)
            (.retain (179595299912762880000 / 772370756866053571))
            (.retain (186002844165112320000 / 772370756866053571))
          )
        )
        (.split 1 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (271783418180613120000 / 772370756866053571))
            (.retain (161460820671068160000 / 772370756866053571))
          )
          (.retain (223764914171750400000 / 772370756866053571))
        )
      )
    )
    (.split 0 (1 / 2)
      (.split 3 (1 / 2)
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (112800920513472000000 / 772370756866053571))
            (.retain (126345366835476480000 / 772370756866053571))
          )
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (245293856432225280000 / 772370756866053571))
              (.retain (145010329352939520000 / 772370756866053571))
            )
            (.retain (79419677247014400000 / 772370756866053571))
          )
        )
        (.split 4 (1 / 2)
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (295842223670999040000 / 772370756866053571))
              (.retain (184934996038517760000 / 772370756866053571))
            )
            (.retain (199964973562997760000 / 772370756866053571))
          )
          (.split 0 (1 / 2)
            (.split 3 (1 / 2)
              (.retain (98581897752837120000 / 772370756866053571))
              (.retain (113963080951111680000 / 772370756866053571))
            )
            (.retain (99559994109004800000 / 772370756866053571))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.retain (119299485599262720000 / 772370756866053571))
          (.split 4 (1 / 2)
            (.retain (189013570211796480000 / 772370756866053571))
            (.retain (85464147612948480000 / 772370756866053571))
          )
        )
        (.split 3 (1 / 2)
          (.retain (112944301945079040000 / 772370756866053571))
          (.retain (125242526722129920000 / 772370756866053571))
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (62937922609 / 100000000000000) := by
  decide +kernel

end C100S009
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
