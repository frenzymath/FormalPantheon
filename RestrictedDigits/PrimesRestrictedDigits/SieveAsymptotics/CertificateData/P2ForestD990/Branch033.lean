import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard544
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard545
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard546
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard547
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard548
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard549
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard550
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard551
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard552
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard553
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard554
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard555
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard556
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard557
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard558
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard559

/-!
# exact P2 forest branch Branch033
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch033

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'right')), 317 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard544.tree
          Shard545.tree
        )
        (.split (0 : Fin 6)
          Shard546.tree
          Shard547.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard548.tree
          Shard549.tree
        )
        (.split (0 : Fin 6)
          Shard550.tree
          Shard551.tree
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard552.tree
          Shard553.tree
        )
        (.split (3 : Fin 6)
          Shard554.tree
          Shard555.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard556.tree
          Shard557.tree
        )
        (.split (0 : Fin 6)
          Shard558.tree
          Shard559.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard544.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard544.root_eq_path] using Shard544.valid
  have hvalid001 :
      Shard545.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard545.root_eq_path] using Shard545.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard546.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard546.root_eq_path] using Shard546.valid
  have hvalid004 :
      Shard547.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard547.root_eq_path] using Shard547.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard548.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard548.root_eq_path] using Shard548.valid
  have hvalid008 :
      Shard549.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard549.root_eq_path] using Shard549.valid
  have hvalid009 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard550.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard550.root_eq_path] using Shard550.valid
  have hvalid011 :
      Shard551.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard551.root_eq_path] using Shard551.valid
  have hvalid012 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard552.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard552.root_eq_path] using Shard552.valid
  have hvalid016 :
      Shard553.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard553.root_eq_path] using Shard553.valid
  have hvalid017 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard554.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard554.root_eq_path] using Shard554.valid
  have hvalid019 :
      Shard555.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard555.root_eq_path] using Shard555.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard556.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard556.root_eq_path] using Shard556.valid
  have hvalid023 :
      Shard557.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard557.root_eq_path] using Shard557.valid
  have hvalid024 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard558.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard558.root_eq_path] using Shard558.valid
  have hvalid026 :
      Shard559.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard559.root_eq_path] using Shard559.valid
  have hvalid027 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
      (9867054873231400335271407 / 8192000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard544.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (188583068580581617194393 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard544.root_eq_path] using Shard544.replay
  have hreplay001 :
      Shard545.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (515131245153809820052713 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard545.root_eq_path] using Shard545.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (188583068580581617194393 / 4096000000000000000000000000 : Rat) + (515131245153809820052713 / 8192000000000000000000000000 : Rat) = (892297382314973054441499 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard546.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (613979874208678594075101 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard546.root_eq_path] using Shard546.replay
  have hreplay004 :
      Shard547.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (645728932552524999089607 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard547.root_eq_path] using Shard547.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (613979874208678594075101 / 8192000000000000000000000000 : Rat) + (645728932552524999089607 / 8192000000000000000000000000 : Rat) = (314927201690300898291177 / 2048000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (892297382314973054441499 / 8192000000000000000000000000 : Rat) + (314927201690300898291177 / 2048000000000000000000000000 : Rat) = (2152006189076176647606207 / 8192000000000000000000000000 : Rat))
  have hreplay007 :
      Shard548.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (41688039936651136999677 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard548.root_eq_path] using Shard548.replay
  have hreplay008 :
      Shard549.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (763628651433809532041067 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard549.root_eq_path] using Shard549.replay
  have hraw009 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (41688039936651136999677 / 512000000000000000000000000 : Rat) + (763628651433809532041067 / 8192000000000000000000000000 : Rat) = (1430637290420227724035899 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard550.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (347216620149856719828873 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard550.root_eq_path] using Shard550.replay
  have hreplay011 :
      Shard551.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (181439388157844385554247 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard551.root_eq_path] using Shard551.replay
  have hraw012 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (347216620149856719828873 / 4096000000000000000000000000 : Rat) + (181439388157844385554247 / 2048000000000000000000000000 : Rat) = (710095396465545490937367 / 4096000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (1430637290420227724035899 / 8192000000000000000000000000 : Rat) + (710095396465545490937367 / 4096000000000000000000000000 : Rat) = (2850828083351318705910633 / 8192000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (2152006189076176647606207 / 8192000000000000000000000000 : Rat) + (2850828083351318705910633 / 8192000000000000000000000000 : Rat) = (125070856810687383837921 / 204800000000000000000000000 : Rat))
  have hreplay015 :
      Shard552.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (853686242978133442131873 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard552.root_eq_path] using Shard552.replay
  have hreplay016 :
      Shard553.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (583086547050217229230191 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard553.root_eq_path] using Shard553.replay
  have hraw017 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (853686242978133442131873 / 16384000000000000000000000000 : Rat) + (583086547050217229230191 / 8192000000000000000000000000 : Rat) = (403971867415713580118451 / 3276800000000000000000000000 : Rat))
  have hreplay018 :
      Shard554.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (672907910687582416105221 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard554.root_eq_path] using Shard554.replay
  have hreplay019 :
      Shard555.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (132570660275396173764207 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard555.root_eq_path] using Shard555.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (672907910687582416105221 / 8192000000000000000000000000 : Rat) + (132570660275396173764207 / 1638400000000000000000000000 : Rat) = (83485075754035205307891 / 512000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (403971867415713580118451 / 3276800000000000000000000000 : Rat) + (83485075754035205307891 / 512000000000000000000000000 : Rat) = (4691381761207694470444767 / 16384000000000000000000000000 : Rat))
  have hreplay022 :
      Shard556.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (898802686030951540158147 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard556.root_eq_path] using Shard556.replay
  have hreplay023 :
      Shard557.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (604712727159273325219707 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard557.root_eq_path] using Shard557.replay
  have hraw024 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (898802686030951540158147 / 16384000000000000000000000000 : Rat) + (604712727159273325219707 / 8192000000000000000000000000 : Rat) = (2108228140349498190597561 / 16384000000000000000000000000 : Rat))
  have hreplay025 :
      Shard558.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (721910390556277552354029 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard558.root_eq_path] using Shard558.replay
  have hreplay026 :
      Shard559.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (371252629734515549439687 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard559.root_eq_path] using Shard559.replay
  have hraw027 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (721910390556277552354029 / 8192000000000000000000000000 : Rat) + (371252629734515549439687 / 4096000000000000000000000000 : Rat) = (1464415650025308651233403 / 8192000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (2108228140349498190597561 / 16384000000000000000000000000 : Rat) + (1464415650025308651233403 / 8192000000000000000000000000 : Rat) = (5037059440400115493064367 / 16384000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (4691381761207694470444767 / 16384000000000000000000000000 : Rat) + (5037059440400115493064367 / 16384000000000000000000000000 : Rat) = (4864220600803904981754567 / 8192000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (125070856810687383837921 / 204800000000000000000000000 : Rat) + (4864220600803904981754567 / 8192000000000000000000000000 : Rat) = (9867054873231400335271407 / 8192000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch033
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
