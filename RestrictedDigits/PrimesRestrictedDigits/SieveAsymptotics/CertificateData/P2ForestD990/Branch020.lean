import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard327
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard328
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard329
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard330
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard331
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard332
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard333
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard334
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard335
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard336
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard337
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard338
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard339

/-!
# exact P2 forest branch Branch020
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch020

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'left')), 308 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        Shard327.tree
        (.split (3 : Fin 6)
          Shard328.tree
          Shard329.tree
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard330.tree
          Shard331.tree
        )
        (.split (4 : Fin 6)
          Shard332.tree
          Shard333.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard334.tree
          Shard335.tree
        )
        (.split (1 : Fin 6)
          Shard336.tree
          Shard337.tree
        )
      )
      (.split (2 : Fin 6)
        Shard338.tree
        Shard339.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard327.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard327.root_eq_path] using Shard327.valid
  have hvalid001 :
      Shard328.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard328.root_eq_path] using Shard328.valid
  have hvalid002 :
      Shard329.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard329.root_eq_path] using Shard329.valid
  have hvalid003 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard330.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard330.root_eq_path] using Shard330.valid
  have hvalid006 :
      Shard331.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard331.root_eq_path] using Shard331.valid
  have hvalid007 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :
      Shard332.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard332.root_eq_path] using Shard332.valid
  have hvalid009 :
      Shard333.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard333.root_eq_path] using Shard333.valid
  have hvalid010 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid004 hvalid011
  have hvalid013 :
      Shard334.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard334.root_eq_path] using Shard334.valid
  have hvalid014 :
      Shard335.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard335.root_eq_path] using Shard335.valid
  have hvalid015 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard336.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard336.root_eq_path] using Shard336.valid
  have hvalid017 :
      Shard337.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard337.root_eq_path] using Shard337.valid
  have hvalid018 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard338.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard338.root_eq_path] using Shard338.valid
  have hvalid021 :
      Shard339.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard339.root_eq_path] using Shard339.valid
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid019 hvalid022
  have hvalid024 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid012 hvalid023
  simpa only [tree] using hvalid024

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (333676292060199655943433 / 1024000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard327.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (38501273943079812291537 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard327.root_eq_path] using Shard327.replay
  have hreplay001 :
      Shard328.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (158741230353800409057663 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard328.root_eq_path] using Shard328.replay
  have hreplay002 :
      Shard329.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (69635192775740334621279 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard329.root_eq_path] using Shard329.replay
  have hraw003 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (158741230353800409057663 / 8192000000000000000000000000 : Rat) + (69635192775740334621279 / 4096000000000000000000000000 : Rat) = (298011615905281078300221 / 8192000000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (38501273943079812291537 / 1024000000000000000000000000 : Rat) + (298011615905281078300221 / 8192000000000000000000000000 : Rat) = (606021807449919576632517 / 8192000000000000000000000000 : Rat))
  have hreplay005 :
      Shard330.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (382298734128274826753169 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard330.root_eq_path] using Shard330.replay
  have hreplay006 :
      Shard331.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (16907845566378854781819 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard331.root_eq_path] using Shard331.replay
  have hraw007 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (382298734128274826753169 / 16384000000000000000000000000 : Rat) + (16907845566378854781819 / 655360000000000000000000000 : Rat) = (201248718321936549074661 / 4096000000000000000000000000 : Rat))
  have hreplay008 :
      Shard332.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (87603767012360957660361 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard332.root_eq_path] using Shard332.replay
  have hreplay009 :
      Shard333.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (31215250217321550385407 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard333.root_eq_path] using Shard333.replay
  have hraw010 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (87603767012360957660361 / 4096000000000000000000000000 : Rat) + (31215250217321550385407 / 1638400000000000000000000000 : Rat) = (331283785111329667247757 / 8192000000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (201248718321936549074661 / 4096000000000000000000000000 : Rat) + (331283785111329667247757 / 8192000000000000000000000000 : Rat) = (733781221755202765397079 / 8192000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay004 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (606021807449919576632517 / 8192000000000000000000000000 : Rat) + (733781221755202765397079 / 8192000000000000000000000000 : Rat) = (334950757301280585507399 / 2048000000000000000000000000 : Rat))
  have hreplay013 :
      Shard334.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (332284853538914001802821 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard334.root_eq_path] using Shard334.replay
  have hreplay014 :
      Shard335.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (333806193870967271914227 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard335.root_eq_path] using Shard335.replay
  have hraw015 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (332284853538914001802821 / 16384000000000000000000000000 : Rat) + (333806193870967271914227 / 16384000000000000000000000000 : Rat) = (83261380926235159214631 / 2048000000000000000000000000 : Rat))
  have hreplay016 :
      Shard336.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (223225452374044270004847 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard336.root_eq_path] using Shard336.replay
  have hreplay017 :
      Shard337.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (185608837764181851766857 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard337.root_eq_path] using Shard337.replay
  have hraw018 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (223225452374044270004847 / 8192000000000000000000000000 : Rat) + (185608837764181851766857 / 8192000000000000000000000000 : Rat) = (51104286267278265221463 / 1024000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (83261380926235159214631 / 2048000000000000000000000000 : Rat) + (51104286267278265221463 / 1024000000000000000000000000 : Rat) = (185469953460791689657557 / 2048000000000000000000000000 : Rat))
  have hreplay020 :
      Shard338.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (73552364188763206414257 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard338.root_eq_path] using Shard338.replay
  have hreplay021 :
      Shard339.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (73379509169563830307653 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard339.root_eq_path] using Shard339.replay
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (73552364188763206414257 / 2048000000000000000000000000 : Rat) + (73379509169563830307653 / 2048000000000000000000000000 : Rat) = (14693187335832703672191 / 204800000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay019 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (185469953460791689657557 / 2048000000000000000000000000 : Rat) + (14693187335832703672191 / 204800000000000000000000000 : Rat) = (332401826819118726379467 / 2048000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay012 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (334950757301280585507399 / 2048000000000000000000000000 : Rat) + (332401826819118726379467 / 2048000000000000000000000000 : Rat) = (333676292060199655943433 / 1024000000000000000000000000 : Rat))
  simpa only [tree] using hreplay024

end Branch020
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
