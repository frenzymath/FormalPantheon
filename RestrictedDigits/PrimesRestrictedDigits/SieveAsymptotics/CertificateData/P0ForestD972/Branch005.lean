import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard051
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard052
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard053
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard054

/-!
# exact P0 forest branch Branch005
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch005

/- Root 2, exact path ((1, 'left'),), 333 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      Shard051.tree
      Shard052.tree
    )
    (.split (4 : Fin 6)
      Shard053.tree
      Shard054.tree
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard051.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard051.root_eq_path] using Shard051.valid
  have hvalid001 :
      Shard052.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard052.root_eq_path] using Shard052.valid
  have hvalid002 :=
    valid_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard053.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard053.root_eq_path] using Shard053.valid
  have hvalid004 :
      Shard054.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard054.root_eq_path] using Shard054.valid
  have hvalid005 :=
    valid_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid005
  simpa only [tree] using hvalid006

theorem replay :
    tree.replayWeightRat ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) (fun _ q => q) =
      (7238362117590620746267199 / 18432000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard051.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (164029703105785394503561 / 2304000000000000000000000000 : Rat) := by
    simpa only [Shard051.root_eq_path] using Shard051.replay
  have hreplay001 :
      Shard052.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ q => q) =
        (49565608896576693903693 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard052.root_eq_path] using Shard052.replay
  have hraw002 :=
    replay_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (164029703105785394503561 / 2304000000000000000000000000 : Rat) + (49565608896576693903693 / 512000000000000000000000000 : Rat) = (774149886280761034140359 / 4608000000000000000000000000 : Rat))
  have hreplay003 :
      Shard053.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ q => q) =
        (1888859017389234786680891 / 18432000000000000000000000000 : Rat) := by
    simpa only [Shard053.root_eq_path] using Shard053.replay
  have hreplay004 :
      Shard054.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ q => q) =
        (281612944384792727878109 / 2304000000000000000000000000 : Rat) := by
    simpa only [Shard054.root_eq_path] using Shard054.replay
  have hraw005 :=
    replay_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (1888859017389234786680891 / 18432000000000000000000000000 : Rat) + (281612944384792727878109 / 2304000000000000000000000000 : Rat) = (460195841385286289967307 / 2048000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (sectionSixP0RootD971 (2 : Fin 3)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (774149886280761034140359 / 4608000000000000000000000000 : Rat) + (460195841385286289967307 / 2048000000000000000000000000 : Rat) = (7238362117590620746267199 / 18432000000000000000000000000 : Rat))
  simpa only [tree] using hreplay006

end Branch005
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
