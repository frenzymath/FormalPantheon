import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard192
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard193
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard194
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard195
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard196
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard197
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard198
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard199
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard200
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard201
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard202
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard203
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard204
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard205
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard206
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard207

/-!
# exact P2 forest branch Branch011
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch011

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'right')), 336 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          Shard192.tree
          Shard193.tree
        )
        (.split (3 : Fin 6)
          Shard194.tree
          Shard195.tree
        )
      )
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard196.tree
          Shard197.tree
        )
        (.split (4 : Fin 6)
          Shard198.tree
          Shard199.tree
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          Shard200.tree
          Shard201.tree
        )
        (.split (3 : Fin 6)
          Shard202.tree
          Shard203.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          Shard204.tree
          Shard205.tree
        )
        (.split (1 : Fin 6)
          Shard206.tree
          Shard207.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
  have hvalid000 :
      Shard192.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard192.root_eq_path] using Shard192.valid
  have hvalid001 :
      Shard193.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard193.root_eq_path] using Shard193.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard194.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard194.root_eq_path] using Shard194.valid
  have hvalid004 :
      Shard195.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard195.root_eq_path] using Shard195.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard196.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard196.root_eq_path] using Shard196.valid
  have hvalid008 :
      Shard197.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard197.root_eq_path] using Shard197.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard198.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard198.root_eq_path] using Shard198.valid
  have hvalid011 :
      Shard199.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard199.root_eq_path] using Shard199.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard200.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard200.root_eq_path] using Shard200.valid
  have hvalid016 :
      Shard201.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard201.root_eq_path] using Shard201.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard202.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard202.root_eq_path] using Shard202.valid
  have hvalid019 :
      Shard203.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard203.root_eq_path] using Shard203.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard204.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard204.root_eq_path] using Shard204.valid
  have hvalid023 :
      Shard205.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard205.root_eq_path] using Shard205.valid
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard206.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard206.root_eq_path] using Shard206.valid
  have hvalid026 :
      Shard207.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard207.root_eq_path] using Shard207.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
      (3385000583974365643363869 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard192.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (65380867536387400670961 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard192.root_eq_path] using Shard192.replay
  have hreplay001 :
      Shard193.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (80876898979521739491843 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard193.root_eq_path] using Shard193.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (65380867536387400670961 / 8192000000000000000000000000 : Rat) + (80876898979521739491843 / 8192000000000000000000000000 : Rat) = (36564441628977285040701 / 2048000000000000000000000000 : Rat))
  have hreplay003 :
      Shard194.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (19095607277007688559313 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard194.root_eq_path] using Shard194.replay
  have hreplay004 :
      Shard195.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (21523986858772077214113 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard195.root_eq_path] using Shard195.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (19095607277007688559313 / 2048000000000000000000000000 : Rat) + (21523986858772077214113 / 3276800000000000000000000000 : Rat) = (260384792509921894545069 / 16384000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (36564441628977285040701 / 2048000000000000000000000000 : Rat) + (260384792509921894545069 / 16384000000000000000000000000 : Rat) = (552900325541740174870677 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Shard196.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (101551295657604758336127 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard196.root_eq_path] using Shard196.replay
  have hreplay008 :
      Shard197.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (40000851028365464500263 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard197.root_eq_path] using Shard197.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (101551295657604758336127 / 8192000000000000000000000000 : Rat) + (40000851028365464500263 / 4096000000000000000000000000 : Rat) = (181552997714335687336653 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard198.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (310812936689523448467 / 20480000000000000000000000 : Rat) := by
    simpa only [Shard198.root_eq_path] using Shard198.replay
  have hreplay011 :
      Shard199.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (92968707230279542647531 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard199.root_eq_path] using Shard199.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (310812936689523448467 / 20480000000000000000000000 : Rat) + (92968707230279542647531 / 8192000000000000000000000000 : Rat) = (217293881906088922034331 / 8192000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (181552997714335687336653 / 8192000000000000000000000000 : Rat) + (217293881906088922034331 / 8192000000000000000000000000 : Rat) = (49855859952553076171373 / 1024000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (552900325541740174870677 / 16384000000000000000000000000 : Rat) + (49855859952553076171373 / 1024000000000000000000000000 : Rat) = (270118816956517878722529 / 3276800000000000000000000000 : Rat))
  have hreplay015 :
      Shard200.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (129818912264712861143967 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard200.root_eq_path] using Shard200.replay
  have hreplay016 :
      Shard201.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (87524217831453408856917 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard201.root_eq_path] using Shard201.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (129818912264712861143967 / 8192000000000000000000000000 : Rat) + (87524217831453408856917 / 8192000000000000000000000000 : Rat) = (54335782524041567500221 / 2048000000000000000000000000 : Rat))
  have hreplay018 :
      Shard202.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (4426090006307559275709 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard202.root_eq_path] using Shard202.replay
  have hreplay019 :
      Shard203.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (24509202308235354922227 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard203.root_eq_path] using Shard203.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (4426090006307559275709 / 256000000000000000000000000 : Rat) + (24509202308235354922227 / 2048000000000000000000000000 : Rat) = (59917922358695829127899 / 2048000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (54335782524041567500221 / 2048000000000000000000000000 : Rat) + (59917922358695829127899 / 2048000000000000000000000000 : Rat) = (2856342622068434915703 / 51200000000000000000000000 : Rat))
  have hreplay022 :
      Shard204.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (134399091467372210463429 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard204.root_eq_path] using Shard204.replay
  have hreplay023 :
      Shard205.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (88750261239126603046047 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard205.root_eq_path] using Shard205.replay
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (134399091467372210463429 / 8192000000000000000000000000 : Rat) + (88750261239126603046047 / 8192000000000000000000000000 : Rat) = (55787338176624703377369 / 2048000000000000000000000000 : Rat))
  have hreplay025 :
      Shard206.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (20269252155292604860977 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard206.root_eq_path] using Shard206.replay
  have hreplay026 :
      Shard207.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (2186063251451236074573 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard207.root_eq_path] using Shard207.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (20269252155292604860977 / 1024000000000000000000000000 : Rat) + (2186063251451236074573 / 102400000000000000000000000 : Rat) = (42129884669804965606707 / 1024000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (55787338176624703377369 / 2048000000000000000000000000 : Rat) + (42129884669804965606707 / 1024000000000000000000000000 : Rat) = (140047107516234634590783 / 2048000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (2856342622068434915703 / 51200000000000000000000000 : Rat) + (140047107516234634590783 / 2048000000000000000000000000 : Rat) = (254300812398972031218903 / 2048000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (270118816956517878722529 / 3276800000000000000000000000 : Rat) + (254300812398972031218903 / 2048000000000000000000000000 : Rat) = (3385000583974365643363869 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch011
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
