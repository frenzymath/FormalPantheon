import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard047
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard048
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard049
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard050

/-!
# exact P0 forest branch Branch004
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch004

/- Root 1, exact path ((0, 'right'),), 337 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (1 : Fin 6)
    (.split (1 : Fin 6)
      Shard047.tree
      Shard048.tree
    )
    (.split (2 : Fin 6)
      Shard049.tree
      Shard050.tree
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard047.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard047.root_eq_path] using Shard047.valid
  have hvalid001 :
      Shard048.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard048.root_eq_path] using Shard048.valid
  have hvalid002 :=
    valid_split (T := ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard049.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard049.root_eq_path] using Shard049.valid
  have hvalid004 :
      Shard050.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard050.root_eq_path] using Shard050.valid
  have hvalid005 :=
    valid_split (T := ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid005
  simpa only [tree] using hvalid006

theorem replay :
    tree.replayWeightRat ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) (fun _ q => q) =
      (14700849470313844927773679 / 36864000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard047.tree.replayWeightRat ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (1333529321983983699557257 / 18432000000000000000000000000 : Rat) := by
    simpa only [Shard047.root_eq_path] using Shard047.replay
  have hreplay001 :
      Shard048.tree.replayWeightRat ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ q => q) =
        (603098277950841049663703 / 6144000000000000000000000000 : Rat) := by
    simpa only [Shard048.root_eq_path] using Shard048.replay
  have hraw002 :=
    replay_split (T := ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (1333529321983983699557257 / 18432000000000000000000000000 : Rat) + (603098277950841049663703 / 6144000000000000000000000000 : Rat) = (1571412077918253424274183 / 9216000000000000000000000000 : Rat))
  have hreplay003 :
      Shard049.tree.replayWeightRat ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (51157765509473976634063 / 491520000000000000000000000 : Rat) := by
    simpa only [Shard049.root_eq_path] using Shard049.replay
  have hreplay004 :
      Shard050.tree.replayWeightRat ((((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (2289184372715141491561111 / 18432000000000000000000000000 : Rat) := by
    simpa only [Shard050.root_eq_path] using Shard050.replay
  have hraw005 :=
    replay_split (T := ((sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (51157765509473976634063 / 491520000000000000000000000 : Rat) + (2289184372715141491561111 / 18432000000000000000000000000 : Rat) = (8415201158640831230676947 / 36864000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (sectionSixP0RootD971 (1 : Fin 3)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (1571412077918253424274183 / 9216000000000000000000000000 : Rat) + (8415201158640831230676947 / 36864000000000000000000000000 : Rat) = (14700849470313844927773679 / 36864000000000000000000000000 : Rat))
  simpa only [tree] using hreplay006

end Branch004
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
