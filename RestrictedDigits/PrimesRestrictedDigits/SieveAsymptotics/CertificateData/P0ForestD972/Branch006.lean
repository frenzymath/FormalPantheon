import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard055
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard056
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard057
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard058

/-!
# exact P0 forest branch Branch006
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch006

/- Root 2, exact path ((1, 'right'),), 303 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      Shard055.tree
      Shard056.tree
    )
    (.split (1 : Fin 6)
      Shard057.tree
      Shard058.tree
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard055.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard055.root_eq_path] using Shard055.valid
  have hvalid001 :
      Shard056.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard056.root_eq_path] using Shard056.valid
  have hvalid002 :=
    valid_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard057.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard057.root_eq_path] using Shard057.valid
  have hvalid004 :
      Shard058.tree.coverValid sectionSixP0LeafValidD970 ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard058.root_eq_path] using Shard058.valid
  have hvalid005 :=
    valid_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  simpa only [tree] using hvalid006

theorem replay :
    tree.replayWeightRat ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) (fun _ q => q) =
      (216509977618534675113329 / 460800000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard055.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ q => q) =
        (465479295471404066020559 / 4608000000000000000000000000 : Rat) := by
    simpa only [Shard055.root_eq_path] using Shard055.replay
  have hreplay001 :
      Shard056.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ q => q) =
        (1105959349822166821355167 / 9216000000000000000000000000 : Rat) := by
    simpa only [Shard056.root_eq_path] using Shard056.replay
  have hraw002 :=
    replay_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (465479295471404066020559 / 4608000000000000000000000000 : Rat) + (1105959349822166821355167 / 9216000000000000000000000000 : Rat) = (407383588152994990679257 / 1843200000000000000000000000 : Rat))
  have hreplay003 :
      Shard057.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (3426467070004904553989269 / 27648000000000000000000000000 : Rat) := by
    simpa only [Shard057.root_eq_path] using Shard057.replay
  have hreplay004 :
      Shard058.tree.replayWeightRat ((((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ q => q) =
        (215836110300765693288851 / 1728000000000000000000000000 : Rat) := by
    simpa only [Shard058.root_eq_path] using Shard058.replay
  have hraw005 :=
    replay_split (T := ((sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (3426467070004904553989269 / 27648000000000000000000000000 : Rat) + (215836110300765693288851 / 1728000000000000000000000000 : Rat) = (458656322321143709774059 / 1843200000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (sectionSixP0RootD971 (2 : Fin 3)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (407383588152994990679257 / 1843200000000000000000000000 : Rat) + (458656322321143709774059 / 1843200000000000000000000000 : Rat) = (216509977618534675113329 / 460800000000000000000000000 : Rat))
  simpa only [tree] using hreplay006

end Branch006
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
