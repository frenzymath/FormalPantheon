import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard045
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard046

/-!
# exact P0 forest branch Branch003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch003

/- Root 1, exact path ((0, 'left'),), 185 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (0 : Fin 6)
    Shard045.tree
    Shard046.tree
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard045.tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard045.root_eq_path] using Shard045.valid
  have hvalid001 :
      Shard046.tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard046.root_eq_path] using Shard046.valid
  have hvalid002 :=
    valid_split (T := (sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid000 hvalid001
  simpa only [tree] using hvalid002

theorem replay :
    tree.replayWeightRat ((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) (fun _ q => q) =
      (1277330541315003459057859 / 6144000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard045.tree.replayWeightRat (((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (581334930794958593383937 / 9216000000000000000000000000 : Rat) := by
    simpa only [Shard045.root_eq_path] using Shard045.replay
  have hreplay001 :
      Shard046.tree.replayWeightRat (((sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (2669321762355093190405703 / 18432000000000000000000000000 : Rat) := by
    simpa only [Shard046.root_eq_path] using Shard046.replay
  have hraw002 :=
    replay_split (T := (sectionSixP0RootD971 (1 : Fin 3)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (581334930794958593383937 / 9216000000000000000000000000 : Rat) + (2669321762355093190405703 / 18432000000000000000000000000 : Rat) = (1277330541315003459057859 / 6144000000000000000000000000 : Rat))
  simpa only [tree] using hreplay002

end Branch003
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
