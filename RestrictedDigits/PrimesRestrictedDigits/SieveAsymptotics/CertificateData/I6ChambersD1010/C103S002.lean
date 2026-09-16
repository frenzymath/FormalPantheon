import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C103S002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C103S002

abbrev label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def root : RationalTetrahedron where
  vertex := ![
    ![(136397197 / 833500000), (37501 / 250000), (54459659 / 416750000)],
    ![(126251 / 500000), (43 / 400), (43 / 400)],
    ![(104999 / 500000), (37501 / 250000), (43 / 400)],
    ![(104999 / 500000), (37501 / 250000), (37501 / 250000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (758 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (2576 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (2576 / 3485));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (379 / 1667));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 1).1 (T.edgePointD1000 1 (758 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 3).2 (T.edgePointD1000 3 (2576 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).2 (T.edgePointD1000 4 (2576 / 3485));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (379 / 1667));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (1 / 2));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (1 / 2));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 0 (2517959 / 4356660)
    (.split 3 (18751 / 21252)
      (.zeroFace 13 0
        (.retain 319)
      )
      (.split 4 (18751 / 21252)
        (.zeroFace 13 0
          (.retain 275)
        )
        (.split 4 (1 / 2)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.split 4 (1 / 2)
                (.split 5 (1 / 2)
                  (.retain (27681802383800000 / 117507884734209))
                  (.retain (25567079439400000 / 117507884734209))
                )
                (.split 3 (1 / 2)
                  (.retain (31553847525200000 / 117507884734209))
                  (.split 0 (1 / 2)
                    (.retain (3036124062400000 / 6912228513777))
                    (.retain (42243213398000000 / 117507884734209))
                  )
                )
              )
              (.split 3 (1 / 2)
                (.split 1 (1 / 2)
                  (.retain (1674718931200000 / 6912228513777))
                  (.split 2 (1 / 2)
                    (.retain (36285432632000000 / 117507884734209))
                    (.retain (39812922768800000 / 117507884734209))
                  )
                )
                (.split 4 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (13830869906400000 / 39169294911403))
                    (.retain (15075352894000000 / 39169294911403))
                  )
                  (.split 0 (1 / 2)
                    (.retain (18282100375200000 / 39169294911403))
                    (.retain (2895241961600000 / 6912228513777))
                  )
                )
              )
            )
            (.split 3 (1 / 2)
              (.split 1 (1 / 2)
                (.split 5 (1 / 2)
                  (.retain (20470802046800000 / 117507884734209))
                  (.retain (19430462528200000 / 117507884734209))
                )
                (.split 2 (1 / 2)
                  (.retain (8587754392200000 / 39169294911403))
                  (.retain (34667030439800000 / 117507884734209))
                )
              )
              (.split 4 (1 / 2)
                (.split 2 (1 / 2)
                  (.retain (9320319916000000 / 39169294911403))
                  (.split 0 (1 / 2)
                    (.retain (36017865582400000 / 117507884734209))
                    (.retain (12884601812800000 / 39169294911403))
                  )
                )
                (.split 0 (1 / 2)
                  (.split 3 (1 / 2)
                    (.retain (14806459051600000 / 39169294911403))
                    (.retain (54405009728800000 / 117507884734209))
                  )
                  (.split 2 (1 / 2)
                    (.retain (42786963302800000 / 117507884734209))
                    (.retain (15086812066000000 / 39169294911403))
                  )
                )
              )
            )
          )
          (.split 3 (1 / 2)
            (.split 5 (1 / 2)
              (.split 0 (1 / 2)
                (.split 4 (1 / 2)
                  (.split 2 (1 / 2)
                    (.retain (18810768118400000 / 39169294911403))
                    (.retain (17102304563600000 / 39169294911403))
                  )
                  (.split 3 (1 / 2)
                    (.retain (15773155739600000 / 39169294911403))
                    (.retain (53045938678400000 / 117507884734209))
                  )
                )
                (.split 2 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (18420602262000000 / 39169294911403))
                    (.retain (50111255750000000 / 117507884734209))
                  )
                  (.split 1 (1 / 2)
                    (.retain (15114711860800000 / 39169294911403))
                    (.retain (49005026369600000 / 117507884734209))
                  )
                )
              )
              (.split 3 (1 / 2)
                (.split 1 (1 / 2)
                  (.retain (27883870400000 / 135533892427))
                  (.split 0 (1 / 2)
                    (.retain (10646191216400000 / 39169294911403))
                    (.retain (36630130833200000 / 117507884734209))
                  )
                )
                (.split 0 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (39092121235600000 / 117507884734209))
                    (.retain (44507978204000000 / 117507884734209))
                  )
                  (.split 1 (1 / 2)
                    (.retain (37851426074000000 / 117507884734209))
                    (.retain (14209523782800000 / 39169294911403))
                  )
                )
              )
            )
            (.split 0 (1 / 2)
              (.split 4 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 2 (1 / 2)
                    (.split 4 (1 / 2)
                      (.retain (25122860076800000 / 39169294911403))
                      (.retain (27517518868800000 / 39169294911403))
                    )
                    (.retain (27100781092800000 / 39169294911403))
                  )
                  (.split 3 (1 / 2)
                    (.retain (68902332585200000 / 117507884734209))
                    (.retain (26953221322000000 / 39169294911403))
                  )
                )
                (.split 3 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (5167427357600000 / 6912228513777))
                    (.retain (25157261389200000 / 39169294911403))
                  )
                  (.split 0 (1 / 2)
                    (.split 4 (1 / 2)
                      (.retain (35025446904800000 / 39169294911403))
                      (.retain (113270610095200000 / 117507884734209))
                    )
                    (.retain (95553801664400000 / 117507884734209))
                  )
                )
              )
              (.split 0 (1 / 2)
                (.split 5 (1 / 2)
                  (.split 4 (1 / 2)
                    (.retain (69510128786800000 / 117507884734209))
                    (.retain (71444108840000000 / 117507884734209))
                  )
                  (.split 1 (1 / 2)
                    (.retain (64717657089200000 / 117507884734209))
                    (.retain (66737332931600000 / 117507884734209))
                  )
                )
                (.split 1 (1 / 2)
                  (.split 5 (1 / 2)
                    (.retain (62774695920400000 / 117507884734209))
                    (.retain (58021394671600000 / 117507884734209))
                  )
                  (.split 2 (1 / 2)
                    (.retain (61400419560800000 / 117507884734209))
                    (.retain (54599230566400000 / 117507884734209))
                  )
                )
              )
            )
          )
        )
      )
    )
    (.zeroFace 13 1
      (.retain 404)
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 3 6) (i6D1006LeafValid 2 3 6) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 3 6) root = (22724966771 / 12500000000000) := by
  decide +kernel

end C103S002
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
