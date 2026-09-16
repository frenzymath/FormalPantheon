import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard645
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard646
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard647
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard648
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard649
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard650
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard651
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard652
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard653
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard654
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard655

/-!
# exact P2 forest branch Branch039
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch039

/- Root 2, exact path ((2, 'right'), (1, 'right'), (2, 'left'), (4, 'right')), 238 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        Shard645.tree
        (.split (3 : Fin 6)
          Shard646.tree
          Shard647.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard648.tree
          Shard649.tree
        )
        (.split (0 : Fin 6)
          Shard650.tree
          Shard651.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        Shard652.tree
        Shard653.tree
      )
      (.split (0 : Fin 6)
        Shard654.tree
        Shard655.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard645.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard645.root_eq_path] using Shard645.valid
  have hvalid001 :
      Shard646.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard646.root_eq_path] using Shard646.valid
  have hvalid002 :
      Shard647.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard647.root_eq_path] using Shard647.valid
  have hvalid003 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard648.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard648.root_eq_path] using Shard648.valid
  have hvalid006 :
      Shard649.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard649.root_eq_path] using Shard649.valid
  have hvalid007 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :
      Shard650.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard650.root_eq_path] using Shard650.valid
  have hvalid009 :
      Shard651.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard651.root_eq_path] using Shard651.valid
  have hvalid010 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid004 hvalid011
  have hvalid013 :
      Shard652.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard652.root_eq_path] using Shard652.valid
  have hvalid014 :
      Shard653.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard653.root_eq_path] using Shard653.valid
  have hvalid015 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard654.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard654.root_eq_path] using Shard654.valid
  have hvalid017 :
      Shard655.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard655.root_eq_path] using Shard655.valid
  have hvalid018 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid012 hvalid019
  simpa only [tree] using hvalid020

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (6105885045201887837477931 / 4096000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard645.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (325341270851621437828413 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard645.root_eq_path] using Shard645.replay
  have hreplay001 :
      Shard646.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (61028215690971089812617 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard646.root_eq_path] using Shard646.replay
  have hreplay002 :
      Shard647.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (11320858846233599220981 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard647.root_eq_path] using Shard647.replay
  have hraw003 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (61028215690971089812617 / 409600000000000000000000000 : Rat) + (11320858846233599220981 / 102400000000000000000000000 : Rat) = (106311651075905486696541 / 409600000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (325341270851621437828413 / 2048000000000000000000000000 : Rat) + (106311651075905486696541 / 409600000000000000000000000 : Rat) = (428449763115574435655559 / 1024000000000000000000000000 : Rat))
  have hreplay005 :
      Shard648.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (259707916257127179042573 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard648.root_eq_path] using Shard648.replay
  have hreplay006 :
      Shard649.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (685873099040572320125463 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard649.root_eq_path] using Shard649.replay
  have hraw007 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (259707916257127179042573 / 2048000000000000000000000000 : Rat) + (685873099040572320125463 / 4096000000000000000000000000 : Rat) = (1205288931554826678210609 / 4096000000000000000000000000 : Rat))
  have hreplay008 :
      Shard650.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (138464240424222903869331 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard650.root_eq_path] using Shard650.replay
  have hreplay009 :
      Shard651.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (14268488579793165820707 / 128000000000000000000000000 : Rat) := by
    simpa only [Shard651.root_eq_path] using Shard651.replay
  have hraw010 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (138464240424222903869331 / 1024000000000000000000000000 : Rat) + (14268488579793165820707 / 128000000000000000000000000 : Rat) = (252612149062568230434987 / 1024000000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (1205288931554826678210609 / 4096000000000000000000000000 : Rat) + (252612149062568230434987 / 1024000000000000000000000000 : Rat) = (2215737527805099599950557 / 4096000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay004 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (428449763115574435655559 / 1024000000000000000000000000 : Rat) + (2215737527805099599950557 / 4096000000000000000000000000 : Rat) = (3929536580267397342572793 / 4096000000000000000000000000 : Rat))
  have hreplay013 :
      Shard652.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (227216676563091289361277 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard652.root_eq_path] using Shard652.replay
  have hreplay014 :
      Shard653.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (332531657145594192084543 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard653.root_eq_path] using Shard653.replay
  have hraw015 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (227216676563091289361277 / 2048000000000000000000000000 : Rat) + (332531657145594192084543 / 2048000000000000000000000000 : Rat) = (27987416685434274072291 / 102400000000000000000000000 : Rat))
  have hreplay016 :
      Shard654.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (30471830831201383519587 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard654.root_eq_path] using Shard654.replay
  have hreplay017 :
      Shard655.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (284651252108948697850053 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard655.root_eq_path] using Shard655.replay
  have hraw018 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (30471830831201383519587 / 256000000000000000000000000 : Rat) + (284651252108948697850053 / 2048000000000000000000000000 : Rat) = (528425898758559766006749 / 2048000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (27987416685434274072291 / 102400000000000000000000000 : Rat) + (528425898758559766006749 / 2048000000000000000000000000 : Rat) = (1088174232467245247452569 / 2048000000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay012 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (3929536580267397342572793 / 4096000000000000000000000000 : Rat) + (1088174232467245247452569 / 2048000000000000000000000000 : Rat) = (6105885045201887837477931 / 4096000000000000000000000000 : Rat))
  simpa only [tree] using hreplay020

end Branch039
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
