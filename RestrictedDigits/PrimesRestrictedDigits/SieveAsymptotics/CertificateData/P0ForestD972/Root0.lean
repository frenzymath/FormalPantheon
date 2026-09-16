import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch002

/-!
# exact P0 forest root Root0
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Root0

/- Root 0, exact path (), 3842 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (1 : Fin 6)
    Branch000.tree
    (.split (0 : Fin 6)
      Branch001.tree
      Branch002.tree
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 (sectionSixP0RootD971 (0 : Fin 3)) = true := by
  have hvalid000 :
      Branch000.tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) = true := by
    exact Branch000.valid
  have hvalid001 :
      Branch001.tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    exact Branch001.valid
  have hvalid002 :
      Branch002.tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    exact Branch002.valid
  have hvalid003 :=
    valid_split (T := (sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := sectionSixP0RootD971 (0 : Fin 3)) (e := (1 : Fin 6)) hvalid000 hvalid003
  simpa only [tree] using hvalid004

theorem replay :
    tree.replayWeightRat (sectionSixP0RootD971 (0 : Fin 3)) (fun _ q => q) =
      (17416105297073493965364567 / 819200000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch000.tree.replayWeightRat ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (12198317535309807058017951 / 1638400000000000000000000000 : Rat) := by
    exact Branch000.replay
  have hreplay001 :
      Branch001.tree.replayWeightRat (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (29070253786467582100033633 / 4915200000000000000000000000 : Rat) := by
    exact Branch001.replay
  have hreplay002 :
      Branch002.tree.replayWeightRat (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (9707856347510990129524979 / 1228800000000000000000000000 : Rat) := by
    exact Branch002.replay
  have hraw003 :=
    replay_split (T := (sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (29070253786467582100033633 / 4915200000000000000000000000 : Rat) + (9707856347510990129524979 / 1228800000000000000000000000 : Rat) = (22633893058837180872711183 / 1638400000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := sectionSixP0RootD971 (0 : Fin 3)) (e := (1 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (12198317535309807058017951 / 1638400000000000000000000000 : Rat) + (22633893058837180872711183 / 1638400000000000000000000000 : Rat) = (17416105297073493965364567 / 819200000000000000000000000 : Rat))
  simpa only [tree] using hreplay004

end Root0
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
