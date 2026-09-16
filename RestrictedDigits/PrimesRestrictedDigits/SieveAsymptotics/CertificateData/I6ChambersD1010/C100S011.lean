import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C100S011
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C100S011

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(774274621 / 4129000000), (180001 / 1500000), (180001 / 1500000)],
    ![(398470879 / 1651600000), (55499 / 600000), (55499 / 600000)],
    ![(212499 / 1000000), (147503 / 1000000), (212499 / 2000000)],
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
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
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
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 0).2 (T.edgePointD1000 0 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (1 / 2)
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (198083112649274880000 / 772370756866053571))
              (.retain (102652895125232640000 / 772370756866053571))
            )
            (.retain (51413842957006080000 / 772370756866053571))
          )
          (.split 4 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (208067434616586240000 / 772370756866053571))
              (.retain (109176413947384320000 / 772370756866053571))
            )
            (.retain (62491429938193920000 / 772370756866053571))
          )
        )
        (.split 4 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (165459090220634880000 / 772370756866053571))
            (.split 2 (1 / 2)
              (.retain (220999679232514560000 / 772370756866053571))
              (.retain (128800312728330240000 / 772370756866053571))
            )
          )
          (.split 1 (1 / 2)
            (.retain (67523078616652800000 / 772370756866053571))
            (.retain (73826221887521280000 / 772370756866053571))
          )
        )
      )
      (.split 4 (1 / 2)
        (.split 5 (1 / 2)
          (.split 4 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (298969071647201280000 / 772370756866053571))
              (.retain (209812500526233600000 / 772370756866053571))
            )
            (.split 3 (1 / 2)
              (.retain (213313671576506880000 / 772370756866053571))
              (.retain (225588417403507200000 / 772370756866053571))
            )
          )
          (.split 1 (1 / 2)
            (.retain (132709096021328640000 / 772370756866053571))
            (.retain (137515401680071680000 / 772370756866053571))
          )
        )
        (.split 0 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (86284220699197440000 / 772370756866053571))
            (.split 4 (1 / 2)
              (.retain (129319997267220480000 / 772370756866053571))
              (.retain (65391774900687360000 / 772370756866053571))
            )
          )
          (.split 3 (1 / 2)
            (.retain (82528669011916800000 / 772370756866053571))
            (.retain (90367693750621440000 / 772370756866053571))
          )
        )
      )
    )
    (.split 3 (1 / 2)
      (.split 1 (1 / 2)
        (.split 5 (1 / 2)
          (.split 2 (1 / 2)
            (.retain (195150164516133120000 / 772370756866053571))
            (.retain (100600016506894080000 / 772370756866053571))
          )
          (.retain (52340727245575680000 / 772370756866053571))
        )
        (.split 0 (1 / 2)
          (.split 5 (1 / 2)
            (.retain (153940818634260480000 / 772370756866053571))
            (.retain (60179834654127360000 / 772370756866053571))
          )
          (.split 2 (1 / 2)
            (.split 5 (1 / 2)
              (.retain (197551444312189440000 / 772370756866053571))
              (.retain (104618773337909760000 / 772370756866053571))
            )
            (.retain (64556371599816960000 / 772370756866053571))
          )
        )
      )
      (.split 0 (1 / 2)
        (.split 3 (1 / 2)
          (.split 1 (1 / 2)
            (.retain (115376690433116160000 / 772370756866053571))
            (.retain (119632536537039360000 / 772370756866053571))
          )
          (.split 4 (1 / 2)
            (.retain (171815308056529920000 / 772370756866053571))
            (.retain (78879923009291520000 / 772370756866053571))
          )
        )
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (112126924428583680000 / 772370756866053571))
            (.retain (116229823419513600000 / 772370756866053571))
          )
          (.split 2 (1 / 2)
            (.retain (159950947432020480000 / 772370756866053571))
            (.retain (69984523558149120000 / 772370756866053571))
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 0) (i6D1006LeafValid 2 3 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 0) root = (15891142729 / 20000000000000) := by
  decide +kernel

end C100S011
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
