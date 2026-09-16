import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard671
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard672
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard673
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard674
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard675
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard676
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard677
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard678
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard679
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard680
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard681
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard682
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard683

/-!
# exact P2 forest branch Branch041
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch041

/- Root 2, exact path ((2, 'right'), (1, 'right'), (2, 'right'), (1, 'right')), 269 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard671.tree
          Shard672.tree
        )
        (.split (0 : Fin 6)
          Shard673.tree
          Shard674.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          Shard675.tree
          Shard676.tree
        )
        Shard677.tree
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard678.tree
          Shard679.tree
        )
        Shard680.tree
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Shard681.tree
          Shard682.tree
        )
        Shard683.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard671.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard671.root_eq_path] using Shard671.valid
  have hvalid001 :
      Shard672.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard672.root_eq_path] using Shard672.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard673.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard673.root_eq_path] using Shard673.valid
  have hvalid004 :
      Shard674.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard674.root_eq_path] using Shard674.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard675.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard675.root_eq_path] using Shard675.valid
  have hvalid008 :
      Shard676.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard676.root_eq_path] using Shard676.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard677.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard677.root_eq_path] using Shard677.valid
  have hvalid011 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid010
  have hvalid012 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard678.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard678.root_eq_path] using Shard678.valid
  have hvalid014 :
      Shard679.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard679.root_eq_path] using Shard679.valid
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard680.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard680.root_eq_path] using Shard680.valid
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard681.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard681.root_eq_path] using Shard681.valid
  have hvalid019 :
      Shard682.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard682.root_eq_path] using Shard682.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard683.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard683.root_eq_path] using Shard683.valid
  have hvalid022 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid017 hvalid022
  have hvalid024 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid012 hvalid023
  simpa only [tree] using hvalid024

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
      (2628969181300875607265601 / 2048000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard671.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (284350282611314713675623 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard671.root_eq_path] using Shard671.replay
  have hreplay001 :
      Shard672.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (142541966307512776664997 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard672.root_eq_path] using Shard672.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (284350282611314713675623 / 4096000000000000000000000000 : Rat) + (142541966307512776664997 / 2048000000000000000000000000 : Rat) = (569434215226340267005617 / 4096000000000000000000000000 : Rat))
  have hreplay003 :
      Shard673.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (208114417785290017459221 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard673.root_eq_path] using Shard673.replay
  have hreplay004 :
      Shard674.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (91075289296032483086043 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard674.root_eq_path] using Shard674.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (208114417785290017459221 / 2048000000000000000000000000 : Rat) + (91075289296032483086043 / 819200000000000000000000000 : Rat) = (871605282050742450348657 / 4096000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (569434215226340267005617 / 4096000000000000000000000000 : Rat) + (871605282050742450348657 / 4096000000000000000000000000 : Rat) = (720519748638541358677137 / 2048000000000000000000000000 : Rat))
  have hreplay007 :
      Shard675.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (395662485890004427614339 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard675.root_eq_path] using Shard675.replay
  have hreplay008 :
      Shard676.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (431031728716928520045957 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard676.root_eq_path] using Shard676.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (395662485890004427614339 / 4096000000000000000000000000 : Rat) + (431031728716928520045957 / 4096000000000000000000000000 : Rat) = (103336776825866618457537 / 512000000000000000000000000 : Rat))
  have hreplay010 :
      Shard677.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (99849727448848401369849 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard677.root_eq_path] using Shard677.replay
  have hraw011 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (103336776825866618457537 / 512000000000000000000000000 : Rat) + (99849727448848401369849 / 1024000000000000000000000000 : Rat) = (306523281100581638284923 / 1024000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (720519748638541358677137 / 2048000000000000000000000000 : Rat) + (306523281100581638284923 / 1024000000000000000000000000 : Rat) = (1333566310839704635246983 / 2048000000000000000000000000 : Rat))
  have hreplay013 :
      Shard678.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (131188338139137565472811 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard678.root_eq_path] using Shard678.replay
  have hreplay014 :
      Shard679.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (310695783903800200421757 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard679.root_eq_path] using Shard679.replay
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (131188338139137565472811 / 1024000000000000000000000000 : Rat) + (310695783903800200421757 / 4096000000000000000000000000 : Rat) = (835449136460350462313001 / 4096000000000000000000000000 : Rat))
  have hreplay016 :
      Shard680.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (175490280991132740127539 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard680.root_eq_path] using Shard680.replay
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (835449136460350462313001 / 4096000000000000000000000000 : Rat) + (175490280991132740127539 / 2048000000000000000000000000 : Rat) = (1186429698442615942568079 / 4096000000000000000000000000 : Rat))
  have hreplay018 :
      Shard681.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (583181623559089096075323 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard681.root_eq_path] using Shard681.replay
  have hreplay019 :
      Shard682.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (173557310101758105609969 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard682.root_eq_path] using Shard682.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (583181623559089096075323 / 4096000000000000000000000000 : Rat) + (173557310101758105609969 / 2048000000000000000000000000 : Rat) = (930296243762605307295261 / 4096000000000000000000000000 : Rat))
  have hreplay021 :
      Shard683.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (59259974839640086771737 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard683.root_eq_path] using Shard683.replay
  have hraw022 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (930296243762605307295261 / 4096000000000000000000000000 : Rat) + (59259974839640086771737 / 512000000000000000000000000 : Rat) = (1404376042479726001469157 / 4096000000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay017 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (1186429698442615942568079 / 4096000000000000000000000000 : Rat) + (1404376042479726001469157 / 4096000000000000000000000000 : Rat) = (647701435230585486009309 / 1024000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay012 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (1333566310839704635246983 / 2048000000000000000000000000 : Rat) + (647701435230585486009309 / 1024000000000000000000000000 : Rat) = (2628969181300875607265601 / 2048000000000000000000000000 : Rat))
  simpa only [tree] using hreplay024

end Branch041
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
