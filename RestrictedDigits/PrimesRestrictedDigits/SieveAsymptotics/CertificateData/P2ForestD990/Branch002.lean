import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard051
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard052
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard053
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard054
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard055
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard056
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard057
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard058
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard059
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard060

/-!
# exact P2 forest branch Branch002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch002

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'left')), 247 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        Shard051.tree
        Shard052.tree
      )
      (.split (3 : Fin 6)
        Shard053.tree
        Shard054.tree
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard055.tree
          Shard056.tree
        )
        Shard057.tree
      )
      (.split (0 : Fin 6)
        Shard058.tree
        (.split (2 : Fin 6)
          Shard059.tree
          Shard060.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard051.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard051.root_eq_path] using Shard051.valid
  have hvalid001 :
      Shard052.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard052.root_eq_path] using Shard052.valid
  have hvalid002 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard053.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard053.root_eq_path] using Shard053.valid
  have hvalid004 :
      Shard054.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard054.root_eq_path] using Shard054.valid
  have hvalid005 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard055.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard055.root_eq_path] using Shard055.valid
  have hvalid008 :
      Shard056.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard056.root_eq_path] using Shard056.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard057.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard057.root_eq_path] using Shard057.valid
  have hvalid011 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid010
  have hvalid012 :
      Shard058.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard058.root_eq_path] using Shard058.valid
  have hvalid013 :
      Shard059.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard059.root_eq_path] using Shard059.valid
  have hvalid014 :
      Shard060.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard060.root_eq_path] using Shard060.valid
  have hvalid015 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid012 hvalid015
  have hvalid017 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid011 hvalid016
  have hvalid018 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid017
  simpa only [tree] using hvalid018

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (15404952536146529953839 / 819200000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard051.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (43570193542621842591 / 40960000000000000000000000 : Rat) := by
    simpa only [Shard051.root_eq_path] using Shard051.replay
  have hreplay001 :
      Shard052.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1932821027757612927 / 1600000000000000000000000 : Rat) := by
    simpa only [Shard052.root_eq_path] using Shard052.replay
  have hraw002 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (43570193542621842591 / 40960000000000000000000000 : Rat) + (1932821027757612927 / 1600000000000000000000000 : Rat) = (465252059266083667611 / 204800000000000000000000000 : Rat))
  have hreplay003 :
      Shard053.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (885334062653858477187 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard053.root_eq_path] using Shard053.replay
  have hreplay004 :
      Shard054.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (701879405665178244141 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard054.root_eq_path] using Shard054.replay
  have hraw005 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (885334062653858477187 / 409600000000000000000000000 : Rat) + (701879405665178244141 / 163840000000000000000000000 : Rat) = (5280065153633608175079 / 819200000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (465252059266083667611 / 204800000000000000000000000 : Rat) + (5280065153633608175079 / 819200000000000000000000000 : Rat) = (7141073390697942845523 / 819200000000000000000000000 : Rat))
  have hreplay007 :
      Shard055.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (102704148174864686967 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard055.root_eq_path] using Shard055.replay
  have hreplay008 :
      Shard056.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (545585063359067349651 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard056.root_eq_path] using Shard056.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (102704148174864686967 / 163840000000000000000000000 : Rat) + (545585063359067349651 / 819200000000000000000000000 : Rat) = (529552902116695392243 / 409600000000000000000000000 : Rat))
  have hreplay010 :
      Shard057.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (680235428188318920687 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard057.root_eq_path] using Shard057.replay
  have hraw011 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (529552902116695392243 / 409600000000000000000000000 : Rat) + (680235428188318920687 / 204800000000000000000000000 : Rat) = (1890023758493333233617 / 409600000000000000000000000 : Rat))
  have hreplay012 :
      Shard058.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2949776744981398933293 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard058.root_eq_path] using Shard058.replay
  have hreplay013 :
      Shard059.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (697932154337492555613 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard059.root_eq_path] using Shard059.replay
  have hreplay014 :
      Shard060.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (52257670571439322011 / 51200000000000000000000000 : Rat) := by
    simpa only [Shard060.root_eq_path] using Shard060.replay
  have hraw015 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (697932154337492555613 / 819200000000000000000000000 : Rat) + (52257670571439322011 / 51200000000000000000000000 : Rat) = (1534054883480521707789 / 819200000000000000000000000 : Rat))
  have hraw016 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay012 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (2949776744981398933293 / 819200000000000000000000000 : Rat) + (1534054883480521707789 / 819200000000000000000000000 : Rat) = (2241915814230960320541 / 409600000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay011 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (1890023758493333233617 / 409600000000000000000000000 : Rat) + (2241915814230960320541 / 409600000000000000000000000 : Rat) = (2065969786362146777079 / 204800000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (7141073390697942845523 / 819200000000000000000000000 : Rat) + (2065969786362146777079 / 204800000000000000000000000 : Rat) = (15404952536146529953839 / 819200000000000000000000000 : Rat))
  simpa only [tree] using hreplay018

end Branch002
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
