import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard574
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard575
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard576
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard577
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard578
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard579
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard580
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard581
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard582
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard583
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard584
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard585
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard586
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard587

/-!
# exact P2 forest branch Branch035
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch035

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'right'), (1, 'right')), 296 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        Shard574.tree
        (.split (0 : Fin 6)
          Shard575.tree
          Shard576.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          Shard577.tree
          Shard578.tree
        )
        Shard579.tree
      )
    )
    (.split (1 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard580.tree
          Shard581.tree
        )
        (.split (2 : Fin 6)
          Shard582.tree
          Shard583.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (0 : Fin 6)
          Shard584.tree
          Shard585.tree
        )
        (.split (0 : Fin 6)
          Shard586.tree
          Shard587.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard574.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard574.root_eq_path] using Shard574.valid
  have hvalid001 :
      Shard575.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard575.root_eq_path] using Shard575.valid
  have hvalid002 :
      Shard576.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard576.root_eq_path] using Shard576.valid
  have hvalid003 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard577.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard577.root_eq_path] using Shard577.valid
  have hvalid006 :
      Shard578.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard578.root_eq_path] using Shard578.valid
  have hvalid007 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :
      Shard579.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard579.root_eq_path] using Shard579.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard580.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard580.root_eq_path] using Shard580.valid
  have hvalid012 :
      Shard581.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard581.root_eq_path] using Shard581.valid
  have hvalid013 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard582.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard582.root_eq_path] using Shard582.valid
  have hvalid015 :
      Shard583.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard583.root_eq_path] using Shard583.valid
  have hvalid016 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :
      Shard584.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard584.root_eq_path] using Shard584.valid
  have hvalid019 :
      Shard585.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard585.root_eq_path] using Shard585.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard586.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard586.root_eq_path] using Shard586.valid
  have hvalid022 :
      Shard587.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard587.root_eq_path] using Shard587.valid
  have hvalid023 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid020 hvalid023
  have hvalid025 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid017 hvalid024
  have hvalid026 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid010 hvalid025
  simpa only [tree] using hvalid026

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
      (207108160483210628569101 / 163840000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard574.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1655172563318640265282767 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard574.root_eq_path] using Shard574.replay
  have hreplay001 :
      Shard575.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (121558121094735339895593 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard575.root_eq_path] using Shard575.replay
  have hreplay002 :
      Shard576.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (1010267089268916225251277 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard576.root_eq_path] using Shard576.replay
  have hraw003 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (121558121094735339895593 / 2048000000000000000000000000 : Rat) + (1010267089268916225251277 / 16384000000000000000000000000 : Rat) = (1982732058026798944416021 / 16384000000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (1655172563318640265282767 / 16384000000000000000000000000 : Rat) + (1982732058026798944416021 / 16384000000000000000000000000 : Rat) = (909476155336359802424697 / 4096000000000000000000000000 : Rat))
  have hreplay005 :
      Shard577.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4842322809750995165469 / 64000000000000000000000000 : Rat) := by
    simpa only [Shard577.root_eq_path] using Shard577.replay
  have hreplay006 :
      Shard578.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (252795672718569843994971 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard578.root_eq_path] using Shard578.replay
  have hraw007 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (4842322809750995165469 / 64000000000000000000000000 : Rat) + (252795672718569843994971 / 4096000000000000000000000000 : Rat) = (562704332542633534584987 / 4096000000000000000000000000 : Rat))
  have hreplay008 :
      Shard579.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1305971776287008371551177 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard579.root_eq_path] using Shard579.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (562704332542633534584987 / 4096000000000000000000000000 : Rat) + (1305971776287008371551177 / 8192000000000000000000000000 : Rat) = (2431380441372275440721151 / 8192000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (909476155336359802424697 / 4096000000000000000000000000 : Rat) + (2431380441372275440721151 / 8192000000000000000000000000 : Rat) = (850066550408999009114109 / 1638400000000000000000000000 : Rat))
  have hreplay011 :
      Shard580.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (173011304527202828175201 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard580.root_eq_path] using Shard580.replay
  have hreplay012 :
      Shard581.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (830012078929305713064939 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard581.root_eq_path] using Shard581.replay
  have hraw013 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (173011304527202828175201 / 2048000000000000000000000000 : Rat) + (830012078929305713064939 / 8192000000000000000000000000 : Rat) = (1522057297038117025765743 / 8192000000000000000000000000 : Rat))
  have hreplay014 :
      Shard582.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (346112740883024961190011 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard582.root_eq_path] using Shard582.replay
  have hreplay015 :
      Shard583.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (833773532350749165002097 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard583.root_eq_path] using Shard583.replay
  have hraw016 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (346112740883024961190011 / 4096000000000000000000000000 : Rat) + (833773532350749165002097 / 8192000000000000000000000000 : Rat) = (1525999014116799087382119 / 8192000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (1522057297038117025765743 / 8192000000000000000000000000 : Rat) + (1525999014116799087382119 / 8192000000000000000000000000 : Rat) = (1524028155577458056573931 / 4096000000000000000000000000 : Rat))
  have hreplay018 :
      Shard584.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (697530667692776151089727 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard584.root_eq_path] using Shard584.replay
  have hreplay019 :
      Shard585.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (171295881866639822779227 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard585.root_eq_path] using Shard585.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (697530667692776151089727 / 8192000000000000000000000000 : Rat) + (171295881866639822779227 / 2048000000000000000000000000 : Rat) = (276542839031867088441327 / 1638400000000000000000000000 : Rat))
  have hreplay021 :
      Shard586.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (803560003183345478433957 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard586.root_eq_path] using Shard586.replay
  have hreplay022 :
      Shard587.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (870744762617939349096051 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard587.root_eq_path] using Shard587.replay
  have hraw023 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (803560003183345478433957 / 8192000000000000000000000000 : Rat) + (870744762617939349096051 / 8192000000000000000000000000 : Rat) = (209288095725160603441251 / 1024000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay020 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (276542839031867088441327 / 1638400000000000000000000000 : Rat) + (209288095725160603441251 / 1024000000000000000000000000 : Rat) = (3057018960960620269736643 / 8192000000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay017 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (1524028155577458056573931 / 4096000000000000000000000000 : Rat) + (3057018960960620269736643 / 8192000000000000000000000000 : Rat) = (1221015054423107276576901 / 1638400000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay010 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (850066550408999009114109 / 1638400000000000000000000000 : Rat) + (1221015054423107276576901 / 1638400000000000000000000000 : Rat) = (207108160483210628569101 / 163840000000000000000000000 : Rat))
  simpa only [tree] using hreplay026

end Branch035
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
