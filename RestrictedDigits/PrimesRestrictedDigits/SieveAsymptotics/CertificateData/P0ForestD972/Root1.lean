import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch003
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch004

/-!
# exact P0 forest root Root1
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Root1

/- Root 1, exact path (), 522 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (0 : Fin 6)
    Branch003.tree
    Branch004.tree
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 (sectionSixP0RootD971 (1 : Fin 3)) = true := by
  have hvalid000 :
      Branch003.tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) = true := by
    exact Branch003.valid
  have hvalid001 :
      Branch004.tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) = true := by
    exact Branch004.valid
  have hvalid002 :=
    valid_split (T := sectionSixP0RootD971 (1 : Fin 3)) (e := (0 : Fin 6)) hvalid000 hvalid001
  simpa only [tree] using hvalid002

theorem replay :
    tree.replayWeightRat (sectionSixP0RootD971 (1 : Fin 3)) (fun _ q => q) =
      (22364832718203865682120833 / 36864000000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch003.tree.replayWeightRat ((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (1277330541315003459057859 / 6144000000000000000000000000 : Rat) := by
    exact Branch003.replay
  have hreplay001 :
      Branch004.tree.replayWeightRat ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (14700849470313844927773679 / 36864000000000000000000000000 : Rat) := by
    exact Branch004.replay
  have hraw002 :=
    replay_split (T := sectionSixP0RootD971 (1 : Fin 3)) (e := (0 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (1277330541315003459057859 / 6144000000000000000000000000 : Rat) + (14700849470313844927773679 / 36864000000000000000000000000 : Rat) = (22364832718203865682120833 / 36864000000000000000000000000 : Rat))
  simpa only [tree] using hreplay002

end Root1
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
