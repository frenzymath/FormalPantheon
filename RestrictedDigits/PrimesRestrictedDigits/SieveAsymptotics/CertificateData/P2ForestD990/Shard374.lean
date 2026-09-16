import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974

/-!
# exact P2 forest shard 374
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Shard374

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'right'), (2, 'left'), (4, 'right'), (3, 'left'), (5, 'right')), 25 retained leaves. -/
def root : RationalTetrahedron where
  vertex := ![
    ![229997 / 2000000, 35001 / 1600000, 35001 / 1600000],
    ![52499 / 500000, 365013 / 8000000, 215007 / 8000000],
    ![52499 / 500000, 29001 / 800000, 29001 / 800000],
    ![439993 / 4000000, 615021 / 16000000, 93003 / 3200000]
  ]

theorem root_eq_path :
    root = (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6) := by
  exact congrArg RationalTetrahedron.mk (by
    decide +kernel :
    root.vertex = ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).vertex)

def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 177773376 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 191894286 / 1000000 }
            )
          )
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 190104285 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 31]
                upper := 198390686 / 1000000 }
            )
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 173496018 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 181627919 / 1000000 }
            )
          )
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 179852148 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 181071590 / 1000000 }
            )
          )
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 171232153 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 172749669 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 172966255 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 15, 9, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
                upper := 176610417 / 1000000 }
            )
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 174076888 / 1000000 }
          )
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 14, 14]
              upper := 160382372 / 1000000 }
          )
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 161799715 / 1000000 }
          )
        )
        (.split (0 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 157609516 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 154612307 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 147579086 / 1000000 }
            )
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          (.retain
            { baseline := 1
              legacy := 1
              middle := ![15, 15, 15, 15, 15, 9, 1, 1]
              inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
              upper := 163152720 / 1000000 }
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 160127835 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 153021933 / 1000000 }
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 162016130 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 166083225 / 1000000 }
            )
          )
          (.split (1 : Fin 6)
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![15, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 162440993 / 1000000 }
            )
            (.retain
              { baseline := 1
                legacy := 1
                middle := ![14, 15, 15, 15, 15, 9, 1, 1]
                inverse := ![2, 2, 2, 2, 2, 2, 2, 14]
                upper := 152855727 / 1000000 }
            )
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 root = true := by
  decide +kernel

theorem replay :
    tree.replayWeightRat root (fun _ p => p.upper) =
      (101348116897546161405423 / 4096000000000000000000000000 : Rat) := by
  decide +kernel

end Shard374
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
