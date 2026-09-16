import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard430
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard431
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard432
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard433
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard434
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard435
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard436
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard437
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard438
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard439
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard440
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard441
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard442
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard443

/-!
# exact P2 forest branch Branch027
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch027

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'right'), (5, 'right'), (2, 'right')), 329 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (1 : Fin 6)
        Shard430.tree
        Shard431.tree
      )
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          Shard432.tree
          Shard433.tree
        )
        (.split (2 : Fin 6)
          Shard434.tree
          Shard435.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Shard436.tree
          Shard437.tree
        )
        (.split (2 : Fin 6)
          Shard438.tree
          Shard439.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard440.tree
          Shard441.tree
        )
        (.split (1 : Fin 6)
          Shard442.tree
          Shard443.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
  have hvalid000 :
      Shard430.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard430.root_eq_path] using Shard430.valid
  have hvalid001 :
      Shard431.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard431.root_eq_path] using Shard431.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard432.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard432.root_eq_path] using Shard432.valid
  have hvalid004 :
      Shard433.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard433.root_eq_path] using Shard433.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :
      Shard434.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard434.root_eq_path] using Shard434.valid
  have hvalid007 :
      Shard435.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard435.root_eq_path] using Shard435.valid
  have hvalid008 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid009
  have hvalid011 :
      Shard436.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard436.root_eq_path] using Shard436.valid
  have hvalid012 :
      Shard437.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard437.root_eq_path] using Shard437.valid
  have hvalid013 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard438.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard438.root_eq_path] using Shard438.valid
  have hvalid015 :
      Shard439.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard439.root_eq_path] using Shard439.valid
  have hvalid016 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :
      Shard440.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard440.root_eq_path] using Shard440.valid
  have hvalid019 :
      Shard441.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard441.root_eq_path] using Shard441.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard442.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard442.root_eq_path] using Shard442.valid
  have hvalid022 :
      Shard443.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard443.root_eq_path] using Shard443.valid
  have hvalid023 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid020 hvalid023
  have hvalid025 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid017 hvalid024
  have hvalid026 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid025
  simpa only [tree] using hvalid026

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
      (704960426602484236893177 / 1024000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard430.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (16426572506319037484979 / 128000000000000000000000000 : Rat) := by
    simpa only [Shard430.root_eq_path] using Shard430.replay
  have hreplay001 :
      Shard431.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (915148475848933871931351 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard431.root_eq_path] using Shard431.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (16426572506319037484979 / 128000000000000000000000000 : Rat) + (915148475848933871931351 / 8192000000000000000000000000 : Rat) = (1966449116253352270970007 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard432.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (398462237801117974225377 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard432.root_eq_path] using Shard432.replay
  have hreplay004 :
      Shard433.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (749588507048681570755521 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard433.root_eq_path] using Shard433.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (398462237801117974225377 / 8192000000000000000000000000 : Rat) + (749588507048681570755521 / 16384000000000000000000000000 : Rat) = (61860519306036700768251 / 655360000000000000000000000 : Rat))
  have hreplay006 :
      Shard434.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (88763150944172006459019 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard434.root_eq_path] using Shard434.replay
  have hreplay007 :
      Shard435.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (637905076989704977382523 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard435.root_eq_path] using Shard435.replay
  have hraw008 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (88763150944172006459019 / 2048000000000000000000000000 : Rat) + (637905076989704977382523 / 16384000000000000000000000000 : Rat) = (53920411381723241162187 / 655360000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (61860519306036700768251 / 655360000000000000000000000 : Rat) + (53920411381723241162187 / 655360000000000000000000000 : Rat) = (57890465343879970965219 / 327680000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (1966449116253352270970007 / 8192000000000000000000000000 : Rat) + (57890465343879970965219 / 327680000000000000000000000 : Rat) = (1706855374925175772550241 / 4096000000000000000000000000 : Rat))
  have hreplay011 :
      Shard436.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (355172824416512808522477 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard436.root_eq_path] using Shard436.replay
  have hreplay012 :
      Shard437.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (12816501887929481156871 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard437.root_eq_path] using Shard437.replay
  have hraw013 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (355172824416512808522477 / 8192000000000000000000000000 : Rat) + (12816501887929481156871 / 327680000000000000000000000 : Rat) = (168896342903687459361063 / 2048000000000000000000000000 : Rat))
  have hreplay014 :
      Shard438.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (152856945638274977356077 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard438.root_eq_path] using Shard438.replay
  have hreplay015 :
      Shard439.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (13443268585518218551689 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard439.root_eq_path] using Shard439.replay
  have hraw016 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (152856945638274977356077 / 4096000000000000000000000000 : Rat) + (13443268585518218551689 / 409600000000000000000000000 : Rat) = (287289631493457162872967 / 4096000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (168896342903687459361063 / 2048000000000000000000000000 : Rat) + (287289631493457162872967 / 4096000000000000000000000000 : Rat) = (625082317300832081595093 / 4096000000000000000000000000 : Rat))
  have hreplay018 :
      Shard440.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (57545182561019611106187 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard440.root_eq_path] using Shard440.replay
  have hreplay019 :
      Shard441.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (94684326280061251731471 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard441.root_eq_path] using Shard441.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (57545182561019611106187 / 1638400000000000000000000000 : Rat) + (94684326280061251731471 / 3276800000000000000000000000 : Rat) = (41954938280420094788769 / 655360000000000000000000000 : Rat))
  have hreplay021 :
      Shard442.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (29428280631466678566423 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard442.root_eq_path] using Shard442.replay
  have hreplay022 :
      Shard443.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (431890109621747146927503 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard443.root_eq_path] using Shard443.replay
  have hraw023 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (29428280631466678566423 / 1024000000000000000000000000 : Rat) + (431890109621747146927503 / 16384000000000000000000000000 : Rat) = (902742599725214003990271 / 16384000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay020 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (41954938280420094788769 / 655360000000000000000000000 : Rat) + (902742599725214003990271 / 16384000000000000000000000000 : Rat) = (243952007091964546713687 / 2048000000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay017 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (625082317300832081595093 / 4096000000000000000000000000 : Rat) + (243952007091964546713687 / 2048000000000000000000000000 : Rat) = (1112986331484761175022467 / 4096000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (1706855374925175772550241 / 4096000000000000000000000000 : Rat) + (1112986331484761175022467 / 4096000000000000000000000000 : Rat) = (704960426602484236893177 / 1024000000000000000000000000 : Rat))
  simpa only [tree] using hreplay026

end Branch027
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
