import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006

/-!
# exact I6 chamber certificate C044S000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1010
namespace C044S000

abbrev label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def root : RationalTetrahedron where
  vertex := ![
    ![(194999 / 1125000), (194999 / 1125000), (194999 / 1125000)],
    ![(55001 / 250000), (69999 / 500000), (69999 / 500000)],
    ![(180001 / 1000000), (180001 / 1000000), (69999 / 500000)],
    ![(180001 / 1000000), (180001 / 1000000), (180001 / 1000000)]
  ]

theorem root_eq_path :
    root = (let T := i6D999OrderedPairRoot;
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (75002 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (75002 / 115005));
            let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (239993 / 360027));
            T) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = (let T := i6D999OrderedPairRoot;
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (2 / 3));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (36667 / 76670));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 4).1 (T.edgePointD1000 4 (75002 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 5).1 (T.edgePointD1000 5 (75002 / 115005));
                   let T := T.replaceVertex (RationalTetrahedron.edgeEndpoints 2).1 (T.edgePointD1000 2 (239993 / 360027));
                   T).vertex)

def tree : RationalTetraClipD1002 16 Rat :=
  (.split 4 (59992 / 120009)
    (.split 5 (59992 / 120009)
      (.zeroFace 3 0
        (.split 0 (59992 / 60017)
          (.split 4 (25 / 60017)
            (.split 5 (25 / 60017)
              (.zeroFace 10 0
                (.retain 231)
              )
              (.retain 230)
            )
            (.retain 231)
          )
          (.split 1 (59992 / 60017)
            (.split 5 (25 / 60017)
              (.zeroFace 10 0
                (.retain 229)
              )
              (.retain 229)
            )
            (.zeroFace 10 1
              (.retain 231)
            )
          )
        )
      )
      (.split 0 (59992 / 60017)
        (.retain (79283051100 / 450067483))
        (.split 1 (59992 / 180001)
          (.split 3 (1 / 2)
            (.split 1 (1 / 2)
              (.retain (15643542849788565000 / 135012367368845051))
              (.retain (22066369636298866875 / 135012367368845051))
            )
            (.split 0 (1 / 2)
              (.split 4 (1 / 2)
                (.retain (26754833713164311250 / 135012367368845051))
                (.retain (26841104763220260000 / 135012367368845051))
              )
              (.split 1 (1 / 2)
                (.retain (24410209465996413750 / 135012367368845051))
                (.retain (26887715313866325000 / 135012367368845051))
              )
            )
          )
          (.split 2 (59992 / 60017)
            (.retain (186048030094425 / 843412544998))
            (.zeroFace 10 1
              (.retain 222)
            )
          )
        )
      )
    )
    (.split 0 (93752 / 105011)
      (.split 3 (5004 / 40003)
        (.split 1 (1 / 2)
          (.split 3 (1 / 2)
            (.retain (144276777176710000 / 2189515745414863))
            (.retain (145452712407020000 / 2189515745414863))
          )
          (.retain (165408490918395000 / 2189515745414863))
        )
        (.split 4 (3753 / 14998)
          (.retain (3934946394500 / 45223949823))
          (.zeroFace 6 0
            (.retain 35)
          )
        )
      )
      (.split 0 (787477489 / 2109431719)
        (.split 3 (1 / 2)
          (.split 5 (1 / 2)
            (.split 0 (1 / 2)
              (.retain (97368345319366440110250 / 793350980777697850309))
              (.retain (131998400448412766054625 / 793350980777697850309))
            )
            (.split 1 (1 / 2)
              (.retain (49362624688989508384500 / 793350980777697850309))
              (.retain (89449759686948079719375 / 793350980777697850309))
            )
          )
          (.split 0 (1 / 2)
            (.split 4 (1 / 2)
              (.retain (102877292762364256522875 / 793350980777697850309))
              (.retain (63822630686495824695375 / 793350980777697850309))
            )
            (.split 1 (1 / 2)
              (.retain (97874896015358484205500 / 793350980777697850309))
              (.retain (132403481786801176049250 / 793350980777697850309))
            )
          )
        )
        (.split 1 (59992 / 180001)
          (.split 5 (1 / 2)
            (.split 2 (1 / 2)
              (.retain (1031652496853497922658750 / 5400899731855908575153))
              (.retain (986181320107411006871250 / 5400899731855908575153))
            )
            (.split 3 (1 / 2)
              (.retain (585189341407859623745625 / 5400899731855908575153))
              (.retain (842775503027971675584375 / 5400899731855908575153))
            )
          )
          (.split 2 (59992 / 60017)
            (.retain (115310396945955923325 / 539824512600879904))
            (.zeroFace 10 1
              (.retain 206)
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid (i6D1005ChamberWalls label 6 0) (i6D1006LeafValid 1 6 0) root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRatD1010 (i6D1005ChamberWalls label 6 0) root = (7384626797 / 25000000000000) := by
  decide +kernel

end C044S000
end PrimesRestrictedDigits.SectionSixI6CertificateD1010
