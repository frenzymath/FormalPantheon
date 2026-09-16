import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard369
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard370
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard371
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard372
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard373
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard374
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard375
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard376
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard377
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard378
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard379
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard380
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard381
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard382
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard383
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard384

/-!
# exact P2 forest branch Branch023
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch023

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'right')), 315 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard369.tree
          Shard370.tree
        )
        (.split (2 : Fin 6)
          Shard371.tree
          Shard372.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard373.tree
          Shard374.tree
        )
        (.split (4 : Fin 6)
          Shard375.tree
          Shard376.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Shard377.tree
          Shard378.tree
        )
        (.split (2 : Fin 6)
          Shard379.tree
          Shard380.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard381.tree
          Shard382.tree
        )
        (.split (0 : Fin 6)
          Shard383.tree
          Shard384.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard369.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard369.root_eq_path] using Shard369.valid
  have hvalid001 :
      Shard370.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard370.root_eq_path] using Shard370.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard371.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard371.root_eq_path] using Shard371.valid
  have hvalid004 :
      Shard372.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard372.root_eq_path] using Shard372.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard373.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard373.root_eq_path] using Shard373.valid
  have hvalid008 :
      Shard374.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard374.root_eq_path] using Shard374.valid
  have hvalid009 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard375.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard375.root_eq_path] using Shard375.valid
  have hvalid011 :
      Shard376.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard376.root_eq_path] using Shard376.valid
  have hvalid012 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard377.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard377.root_eq_path] using Shard377.valid
  have hvalid016 :
      Shard378.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard378.root_eq_path] using Shard378.valid
  have hvalid017 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard379.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard379.root_eq_path] using Shard379.valid
  have hvalid019 :
      Shard380.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard380.root_eq_path] using Shard380.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard381.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard381.root_eq_path] using Shard381.valid
  have hvalid023 :
      Shard382.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard382.root_eq_path] using Shard382.valid
  have hvalid024 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard383.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard383.root_eq_path] using Shard383.valid
  have hvalid026 :
      Shard384.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard384.root_eq_path] using Shard384.valid
  have hvalid027 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
      (580794912688643811663273 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard369.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (37236360218588115031593 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard369.root_eq_path] using Shard369.replay
  have hreplay001 :
      Shard370.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (31119168652803805879881 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard370.root_eq_path] using Shard370.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (37236360218588115031593 / 2048000000000000000000000000 : Rat) + (31119168652803805879881 / 1638400000000000000000000000 : Rat) = (304541284138371489525777 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard371.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (92529869600036440297341 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard371.root_eq_path] using Shard371.replay
  have hreplay004 :
      Shard372.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (179961725253363180736581 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard372.root_eq_path] using Shard372.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (92529869600036440297341 / 4096000000000000000000000000 : Rat) + (179961725253363180736581 / 8192000000000000000000000000 : Rat) = (365021464453436061331263 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (304541284138371489525777 / 8192000000000000000000000000 : Rat) + (365021464453436061331263 / 8192000000000000000000000000 : Rat) = (8369534357397594385713 / 102400000000000000000000000 : Rat))
  have hreplay007 :
      Shard373.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (34559070201137025676233 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard373.root_eq_path] using Shard373.replay
  have hreplay008 :
      Shard374.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (101348116897546161405423 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard374.root_eq_path] using Shard374.replay
  have hraw009 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (34559070201137025676233 / 1638400000000000000000000000 : Rat) + (101348116897546161405423 / 4096000000000000000000000000 : Rat) = (375491584800777451192011 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard375.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (80161885101799740907197 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard375.root_eq_path] using Shard375.replay
  have hreplay011 :
      Shard376.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (164041649673421572856089 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard376.root_eq_path] using Shard376.replay
  have hraw012 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (80161885101799740907197 / 4096000000000000000000000000 : Rat) + (164041649673421572856089 / 8192000000000000000000000000 : Rat) = (324365419877021054670483 / 8192000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (375491584800777451192011 / 8192000000000000000000000000 : Rat) + (324365419877021054670483 / 8192000000000000000000000000 : Rat) = (349928502338899252931247 / 4096000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (8369534357397594385713 / 102400000000000000000000000 : Rat) + (349928502338899252931247 / 4096000000000000000000000000 : Rat) = (684709876634803028359767 / 4096000000000000000000000000 : Rat))
  have hreplay015 :
      Shard377.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (26982297431288257513203 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard377.root_eq_path] using Shard377.replay
  have hreplay016 :
      Shard378.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (189493081847023851845991 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard378.root_eq_path] using Shard378.replay
  have hraw017 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (26982297431288257513203 / 1024000000000000000000000000 : Rat) + (189493081847023851845991 / 8192000000000000000000000000 : Rat) = (81070292259465982390323 / 1638400000000000000000000000 : Rat))
  have hreplay018 :
      Shard379.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (187182861569491365192393 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard379.root_eq_path] using Shard379.replay
  have hreplay019 :
      Shard380.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (206099741550143635946073 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard380.root_eq_path] using Shard380.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (187182861569491365192393 / 8192000000000000000000000000 : Rat) + (206099741550143635946073 / 8192000000000000000000000000 : Rat) = (196641301559817500569233 / 4096000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (81070292259465982390323 / 1638400000000000000000000000 : Rat) + (196641301559817500569233 / 4096000000000000000000000000 : Rat) = (798634064416964913090081 / 8192000000000000000000000000 : Rat))
  have hreplay022 :
      Shard381.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (4254771959779341107511 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard381.root_eq_path] using Shard381.replay
  have hreplay023 :
      Shard382.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (188110788364489903996887 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard382.root_eq_path] using Shard382.replay
  have hraw024 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (4254771959779341107511 / 204800000000000000000000000 : Rat) + (188110788364489903996887 / 8192000000000000000000000000 : Rat) = (358301666755663548297327 / 8192000000000000000000000000 : Rat))
  have hreplay025 :
      Shard383.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (9094993333867444594887 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard383.root_eq_path] using Shard383.replay
  have hreplay026 :
      Shard384.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (195719212323635648311683 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard384.root_eq_path] using Shard384.replay
  have hraw027 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (9094993333867444594887 / 409600000000000000000000000 : Rat) + (195719212323635648311683 / 8192000000000000000000000000 : Rat) = (377619079000984540209423 / 8192000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (358301666755663548297327 / 8192000000000000000000000000 : Rat) + (377619079000984540209423 / 8192000000000000000000000000 : Rat) = (2943682983026592354027 / 32768000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (798634064416964913090081 / 8192000000000000000000000000 : Rat) + (2943682983026592354027 / 32768000000000000000000000 : Rat) = (1534554810173613001596831 / 8192000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (684709876634803028359767 / 4096000000000000000000000000 : Rat) + (1534554810173613001596831 / 8192000000000000000000000000 : Rat) = (580794912688643811663273 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch023
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
