import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard417
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard418
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard419
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard420
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard421
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard422
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard423
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard424
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard425
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard426
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard427
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard428
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard429

/-!
# exact P2 forest branch Branch026
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch026

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'left')), 302 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          Shard417.tree
          Shard418.tree
        )
        Shard419.tree
      )
      (.split (1 : Fin 6)
        Shard420.tree
        (.split (4 : Fin 6)
          Shard421.tree
          Shard422.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard423.tree
          Shard424.tree
        )
        (.split (3 : Fin 6)
          Shard425.tree
          Shard426.tree
        )
      )
      (.split (3 : Fin 6)
        Shard427.tree
        (.split (4 : Fin 6)
          Shard428.tree
          Shard429.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
  have hvalid000 :
      Shard417.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard417.root_eq_path] using Shard417.valid
  have hvalid001 :
      Shard418.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard418.root_eq_path] using Shard418.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard419.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard419.root_eq_path] using Shard419.valid
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid002 hvalid003
  have hvalid005 :
      Shard420.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard420.root_eq_path] using Shard420.valid
  have hvalid006 :
      Shard421.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard421.root_eq_path] using Shard421.valid
  have hvalid007 :
      Shard422.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard422.root_eq_path] using Shard422.valid
  have hvalid008 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard423.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard423.root_eq_path] using Shard423.valid
  have hvalid012 :
      Shard424.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard424.root_eq_path] using Shard424.valid
  have hvalid013 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard425.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard425.root_eq_path] using Shard425.valid
  have hvalid015 :
      Shard426.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard426.root_eq_path] using Shard426.valid
  have hvalid016 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :
      Shard427.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard427.root_eq_path] using Shard427.valid
  have hvalid019 :
      Shard428.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard428.root_eq_path] using Shard428.valid
  have hvalid020 :
      Shard429.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard429.root_eq_path] using Shard429.valid
  have hvalid021 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid019 hvalid020
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid021
  have hvalid023 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid022
  have hvalid024 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid023
  simpa only [tree] using hvalid024

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
      (3300998390904745741653873 / 4096000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard417.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1022508762748147664777853 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard417.root_eq_path] using Shard417.replay
  have hreplay001 :
      Shard418.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1942008476658864150483 / 32000000000000000000000000 : Rat) := by
    simpa only [Shard418.root_eq_path] using Shard418.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (1022508762748147664777853 / 16384000000000000000000000000 : Rat) + (1942008476658864150483 / 32000000000000000000000000 : Rat) = (2016817102797486109825149 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard419.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (988546356219046194058509 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard419.root_eq_path] using Shard419.replay
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay002 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (2016817102797486109825149 / 16384000000000000000000000000 : Rat) + (988546356219046194058509 / 8192000000000000000000000000 : Rat) = (3993909815235578497942167 / 16384000000000000000000000000 : Rat))
  have hreplay005 :
      Shard420.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1040546475572003419107303 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard420.root_eq_path] using Shard420.replay
  have hreplay006 :
      Shard421.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (420647691659442140830977 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard421.root_eq_path] using Shard421.replay
  have hreplay007 :
      Shard422.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (845257318113140924385537 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard422.root_eq_path] using Shard422.replay
  have hraw008 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (420647691659442140830977 / 8192000000000000000000000000 : Rat) + (845257318113140924385537 / 16384000000000000000000000000 : Rat) = (1686552701432025206047491 / 16384000000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (1040546475572003419107303 / 8192000000000000000000000000 : Rat) + (1686552701432025206047491 / 16384000000000000000000000000 : Rat) = (3767645652576032044262097 / 16384000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (3993909815235578497942167 / 16384000000000000000000000000 : Rat) + (3767645652576032044262097 / 16384000000000000000000000000 : Rat) = (970194433476451317775533 / 2048000000000000000000000000 : Rat))
  have hreplay011 :
      Shard423.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (124784383059836691453 / 2560000000000000000000000 : Rat) := by
    simpa only [Shard423.root_eq_path] using Shard423.replay
  have hreplay012 :
      Shard424.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (775294289859992798510829 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard424.root_eq_path] using Shard424.replay
  have hraw013 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (124784383059836691453 / 2560000000000000000000000 : Rat) + (775294289859992798510829 / 16384000000000000000000000000 : Rat) = (1573914341442947623810029 / 16384000000000000000000000000 : Rat))
  have hreplay014 :
      Shard425.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (75883796773655968244619 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard425.root_eq_path] using Shard425.replay
  have hreplay015 :
      Shard426.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (350972440714092381415461 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard426.root_eq_path] using Shard426.replay
  have hraw016 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (75883796773655968244619 / 1638400000000000000000000000 : Rat) + (350972440714092381415461 / 8192000000000000000000000000 : Rat) = (182597856145593055659639 / 2048000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (1573914341442947623810029 / 16384000000000000000000000000 : Rat) + (182597856145593055659639 / 2048000000000000000000000000 : Rat) = (3034697190607692069087141 / 16384000000000000000000000000 : Rat))
  have hreplay018 :
      Shard427.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (666178342069700692249713 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard427.root_eq_path] using Shard427.replay
  have hreplay019 :
      Shard428.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (576884035193759181733743 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard428.root_eq_path] using Shard428.replay
  have hreplay020 :
      Shard429.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (249250092933259894545459 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard429.root_eq_path] using Shard429.replay
  have hraw021 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay019 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (576884035193759181733743 / 16384000000000000000000000000 : Rat) + (249250092933259894545459 / 8192000000000000000000000000 : Rat) = (1075384221060278970824661 / 16384000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (666178342069700692249713 / 8192000000000000000000000000 : Rat) + (1075384221060278970824661 / 16384000000000000000000000000 : Rat) = (2407740905199680355324087 / 16384000000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (3034697190607692069087141 / 16384000000000000000000000000 : Rat) + (2407740905199680355324087 / 16384000000000000000000000000 : Rat) = (1360609523951843106102807 / 4096000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (970194433476451317775533 / 2048000000000000000000000000 : Rat) + (1360609523951843106102807 / 4096000000000000000000000000 : Rat) = (3300998390904745741653873 / 4096000000000000000000000000 : Rat))
  simpa only [tree] using hreplay024

end Branch026
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
