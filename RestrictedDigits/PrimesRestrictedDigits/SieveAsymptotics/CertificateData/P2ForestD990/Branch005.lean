import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard096
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard097
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard098
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard099
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard100
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard101
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard102
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard103
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard104
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard105
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard106
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard107
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard108
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard109
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard110
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard111
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard112

/-!
# exact P2 forest branch Branch005
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch005

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'right')), 356 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (0 : Fin 6)
      (.split (2 : Fin 6)
        (.split (2 : Fin 6)
          Shard096.tree
          (.split (3 : Fin 6)
            Shard097.tree
            Shard098.tree
          )
        )
        (.split (0 : Fin 6)
          (.split (1 : Fin 6)
            Shard099.tree
            Shard100.tree
          )
          Shard101.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            Shard102.tree
            Shard103.tree
          )
          Shard104.tree
        )
        (.split (1 : Fin 6)
          Shard105.tree
          Shard106.tree
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          Shard107.tree
          (.split (3 : Fin 6)
            Shard108.tree
            Shard109.tree
          )
        )
        Shard110.tree
      )
      (.split (1 : Fin 6)
        Shard111.tree
        Shard112.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard096.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard096.root_eq_path] using Shard096.valid
  have hvalid001 :
      Shard097.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard097.root_eq_path] using Shard097.valid
  have hvalid002 :
      Shard098.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard098.root_eq_path] using Shard098.valid
  have hvalid003 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard099.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard099.root_eq_path] using Shard099.valid
  have hvalid006 :
      Shard100.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard100.root_eq_path] using Shard100.valid
  have hvalid007 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :
      Shard101.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard101.root_eq_path] using Shard101.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard102.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard102.root_eq_path] using Shard102.valid
  have hvalid012 :
      Shard103.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard103.root_eq_path] using Shard103.valid
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard104.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard104.root_eq_path] using Shard104.valid
  have hvalid015 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard105.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard105.root_eq_path] using Shard105.valid
  have hvalid017 :
      Shard106.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard106.root_eq_path] using Shard106.valid
  have hvalid018 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid010 hvalid019
  have hvalid021 :
      Shard107.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard107.root_eq_path] using Shard107.valid
  have hvalid022 :
      Shard108.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard108.root_eq_path] using Shard108.valid
  have hvalid023 :
      Shard109.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard109.root_eq_path] using Shard109.valid
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid021 hvalid024
  have hvalid026 :
      Shard110.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard110.root_eq_path] using Shard110.valid
  have hvalid027 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :
      Shard111.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard111.root_eq_path] using Shard111.valid
  have hvalid029 :
      Shard112.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard112.root_eq_path] using Shard112.valid
  have hvalid030 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid027 hvalid030
  have hvalid032 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid020 hvalid031
  simpa only [tree] using hvalid032

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
      (48892431021838685053839 / 409600000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard096.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (4940245459281439273923 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard096.root_eq_path] using Shard096.replay
  have hreplay001 :
      Shard097.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (4610494225132513567641 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard097.root_eq_path] using Shard097.replay
  have hreplay002 :
      Shard098.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (356025171196456775937 / 65536000000000000000000000 : Rat) := by
    simpa only [Shard098.root_eq_path] using Shard098.replay
  have hraw003 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (4610494225132513567641 / 1638400000000000000000000000 : Rat) + (356025171196456775937 / 65536000000000000000000000 : Rat) = (6755561752521966483033 / 819200000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (4940245459281439273923 / 819200000000000000000000000 : Rat) + (6755561752521966483033 / 819200000000000000000000000 : Rat) = (2923951802950851439239 / 204800000000000000000000000 : Rat))
  have hreplay005 :
      Shard099.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4010288397763249723671 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard099.root_eq_path] using Shard099.replay
  have hreplay006 :
      Shard100.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (12499317681673084194537 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard100.root_eq_path] using Shard100.replay
  have hraw007 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (4010288397763249723671 / 819200000000000000000000000 : Rat) + (12499317681673084194537 / 1638400000000000000000000000 : Rat) = (20519894477199583641879 / 1638400000000000000000000000 : Rat))
  have hreplay008 :
      Shard101.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (202815287430966142911 / 16384000000000000000000000 : Rat) := by
    simpa only [Shard101.root_eq_path] using Shard101.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (20519894477199583641879 / 1638400000000000000000000000 : Rat) + (202815287430966142911 / 16384000000000000000000000 : Rat) = (40801423220296197932979 / 1638400000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (2923951802950851439239 / 204800000000000000000000000 : Rat) + (40801423220296197932979 / 1638400000000000000000000000 : Rat) = (64193037643903009446891 / 1638400000000000000000000000 : Rat))
  have hreplay011 :
      Shard102.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2396269981094354328843 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard102.root_eq_path] using Shard102.replay
  have hreplay012 :
      Shard103.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (960606621865972373193 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard103.root_eq_path] using Shard103.replay
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (2396269981094354328843 / 1638400000000000000000000000 : Rat) + (960606621865972373193 / 409600000000000000000000000 : Rat) = (1247739293711648764323 / 327680000000000000000000000 : Rat))
  have hreplay014 :
      Shard104.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (14581358273612997696951 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard104.root_eq_path] using Shard104.replay
  have hraw015 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (1247739293711648764323 / 327680000000000000000000000 : Rat) + (14581358273612997696951 / 1638400000000000000000000000 : Rat) = (10410027371085620759283 / 819200000000000000000000000 : Rat))
  have hreplay016 :
      Shard105.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (14305423880446453468791 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard105.root_eq_path] using Shard105.replay
  have hreplay017 :
      Shard106.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (12218779587547304331219 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard106.root_eq_path] using Shard106.replay
  have hraw018 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (14305423880446453468791 / 1638400000000000000000000000 : Rat) + (12218779587547304331219 / 819200000000000000000000000 : Rat) = (38742983055541062131229 / 1638400000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (10410027371085620759283 / 819200000000000000000000000 : Rat) + (38742983055541062131229 / 1638400000000000000000000000 : Rat) = (11912607559542460729959 / 327680000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay010 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (64193037643903009446891 / 1638400000000000000000000000 : Rat) + (11912607559542460729959 / 327680000000000000000000000 : Rat) = (61878037720807656548343 / 819200000000000000000000000 : Rat))
  have hreplay021 :
      Shard107.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1806809614594278121773 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard107.root_eq_path] using Shard107.replay
  have hreplay022 :
      Shard108.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (647986734997690934439 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard108.root_eq_path] using Shard108.replay
  have hreplay023 :
      Shard109.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (6141008122180849909431 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard109.root_eq_path] using Shard109.replay
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (647986734997690934439 / 655360000000000000000000000 : Rat) + (6141008122180849909431 / 3276800000000000000000000000 : Rat) = (4690470898584652290813 / 1638400000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay021 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (1806809614594278121773 / 1638400000000000000000000000 : Rat) + (4690470898584652290813 / 1638400000000000000000000000 : Rat) = (3248640256589465206293 / 819200000000000000000000000 : Rat))
  have hreplay026 :
      Shard110.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (5501309631251767118577 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard110.root_eq_path] using Shard110.replay
  have hraw027 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (3248640256589465206293 / 819200000000000000000000000 : Rat) + (5501309631251767118577 / 409600000000000000000000000 : Rat) = (14251259519092999443447 / 819200000000000000000000000 : Rat))
  have hreplay028 :
      Shard111.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4250523133228361606001 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard111.root_eq_path] using Shard111.replay
  have hreplay029 :
      Shard112.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (6577259268659995451943 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard112.root_eq_path] using Shard112.replay
  have hraw030 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (4250523133228361606001 / 409600000000000000000000000 : Rat) + (6577259268659995451943 / 409600000000000000000000000 : Rat) = (1353472800236044632243 / 51200000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay027 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (14251259519092999443447 / 819200000000000000000000000 : Rat) + (1353472800236044632243 / 51200000000000000000000000 : Rat) = (7181364864573942711867 / 163840000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay020 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (61878037720807656548343 / 819200000000000000000000000 : Rat) + (7181364864573942711867 / 163840000000000000000000000 : Rat) = (48892431021838685053839 / 409600000000000000000000000 : Rat))
  simpa only [tree] using hreplay032

end Branch005
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
