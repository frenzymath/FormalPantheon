import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch005
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Branch006

/-!
# exact P0 forest root Root2
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Root2

/- Root 2, exact path (), 636 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (1 : Fin 6)
    Branch005.tree
    Branch006.tree
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 (sectionSixP0RootD971 (2 : Fin 3)) = true := by
  have hvalid000 :
      Branch005.tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) = true := by
    exact Branch005.valid
  have hvalid001 :
      Branch006.tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) = true := by
    exact Branch006.valid
  have hvalid002 :=
    valid_split (T := sectionSixP0RootD971 (2 : Fin 3)) (e := (1 : Fin 6)) hvalid000 hvalid001
  simpa only [tree] using hvalid002

theorem replay :
    tree.replayWeightRat (sectionSixP0RootD971 (2 : Fin 3)) (fun _ q => q) =
      (15898761222332007750800359 / 18432000000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch005.tree.replayWeightRat ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (7238362117590620746267199 / 18432000000000000000000000000 : Rat) := by
    exact Branch005.replay
  have hreplay001 :
      Branch006.tree.replayWeightRat ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) (fun _ q => q) =
        (216509977618534675113329 / 460800000000000000000000000 : Rat) := by
    exact Branch006.replay
  have hraw002 :=
    replay_split (T := sectionSixP0RootD971 (2 : Fin 3)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (7238362117590620746267199 / 18432000000000000000000000000 : Rat) + (216509977618534675113329 / 460800000000000000000000000 : Rat) = (15898761222332007750800359 / 18432000000000000000000000000 : Rat))
  simpa only [tree] using hreplay002

end Root2
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
