import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard017
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard018
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard019
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard020
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard021
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard022
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard023
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard024
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard025
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard026
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard027
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard028
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard029
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard030
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard031
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard032

/-!
# exact P2 forest branch Branch000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch000

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'left')), 372 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard017.tree
          Shard018.tree
        )
        (.split (1 : Fin 6)
          Shard019.tree
          Shard020.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          Shard021.tree
          Shard022.tree
        )
        (.split (1 : Fin 6)
          Shard023.tree
          Shard024.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard025.tree
          Shard026.tree
        )
        (.split (3 : Fin 6)
          Shard027.tree
          Shard028.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          Shard029.tree
          Shard030.tree
        )
        (.split (1 : Fin 6)
          Shard031.tree
          Shard032.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard017.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard017.root_eq_path] using Shard017.valid
  have hvalid001 :
      Shard018.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard018.root_eq_path] using Shard018.valid
  have hvalid002 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard019.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard019.root_eq_path] using Shard019.valid
  have hvalid004 :
      Shard020.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard020.root_eq_path] using Shard020.valid
  have hvalid005 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard021.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard021.root_eq_path] using Shard021.valid
  have hvalid008 :
      Shard022.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard022.root_eq_path] using Shard022.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard023.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard023.root_eq_path] using Shard023.valid
  have hvalid011 :
      Shard024.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard024.root_eq_path] using Shard024.valid
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard025.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard025.root_eq_path] using Shard025.valid
  have hvalid016 :
      Shard026.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard026.root_eq_path] using Shard026.valid
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard027.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard027.root_eq_path] using Shard027.valid
  have hvalid019 :
      Shard028.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard028.root_eq_path] using Shard028.valid
  have hvalid020 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard029.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard029.root_eq_path] using Shard029.valid
  have hvalid023 :
      Shard030.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard030.root_eq_path] using Shard030.valid
  have hvalid024 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard031.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard031.root_eq_path] using Shard031.valid
  have hvalid026 :
      Shard032.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard032.root_eq_path] using Shard032.valid
  have hvalid027 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
      (104877929457854515800189 / 819200000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard017.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2631584284210302981219 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard017.root_eq_path] using Shard017.replay
  have hreplay001 :
      Shard018.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (3581935617433753865241 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard018.root_eq_path] using Shard018.replay
  have hraw002 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (2631584284210302981219 / 409600000000000000000000000 : Rat) + (3581935617433753865241 / 409600000000000000000000000 : Rat) = (310675995082202842323 / 20480000000000000000000000 : Rat))
  have hreplay003 :
      Shard019.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7650532099398764535201 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard019.root_eq_path] using Shard019.replay
  have hreplay004 :
      Shard020.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (3300181599629781954549 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard020.root_eq_path] using Shard020.replay
  have hraw005 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (7650532099398764535201 / 1638400000000000000000000000 : Rat) + (3300181599629781954549 / 409600000000000000000000000 : Rat) = (20851258497917892353397 / 1638400000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (310675995082202842323 / 20480000000000000000000000 : Rat) + (20851258497917892353397 / 1638400000000000000000000000 : Rat) = (45705338104494119739237 / 1638400000000000000000000000 : Rat))
  have hreplay007 :
      Shard021.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (15041502708909654197187 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard021.root_eq_path] using Shard021.replay
  have hreplay008 :
      Shard022.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (8506044666875588775723 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard022.root_eq_path] using Shard022.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (15041502708909654197187 / 1638400000000000000000000000 : Rat) + (8506044666875588775723 / 819200000000000000000000000 : Rat) = (32053592042660831748633 / 1638400000000000000000000000 : Rat))
  have hreplay010 :
      Shard023.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (3176979926769263480481 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard023.root_eq_path] using Shard023.replay
  have hreplay011 :
      Shard024.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1834013129028915596751 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard024.root_eq_path] using Shard024.replay
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (3176979926769263480481 / 409600000000000000000000000 : Rat) + (1834013129028915596751 / 163840000000000000000000000 : Rat) = (15524025498683104944717 / 819200000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (32053592042660831748633 / 1638400000000000000000000000 : Rat) + (15524025498683104944717 / 819200000000000000000000000 : Rat) = (63101643040027041638067 / 1638400000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (45705338104494119739237 / 1638400000000000000000000000 : Rat) + (63101643040027041638067 / 1638400000000000000000000000 : Rat) = (13600872643065145172163 / 204800000000000000000000000 : Rat))
  have hreplay015 :
      Shard025.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2230551662029247358351 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard025.root_eq_path] using Shard025.replay
  have hreplay016 :
      Shard026.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (6350356706802126434757 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard026.root_eq_path] using Shard026.replay
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (2230551662029247358351 / 409600000000000000000000000 : Rat) + (6350356706802126434757 / 819200000000000000000000000 : Rat) = (10811460030860621151459 / 819200000000000000000000000 : Rat))
  have hreplay018 :
      Shard027.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (1515391357024083813219 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard027.root_eq_path] using Shard027.replay
  have hreplay019 :
      Shard028.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (5845756771085543357067 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard028.root_eq_path] using Shard028.replay
  have hraw020 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (1515391357024083813219 / 409600000000000000000000000 : Rat) + (5845756771085543357067 / 819200000000000000000000000 : Rat) = (1775307897026742196701 / 163840000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (10811460030860621151459 / 819200000000000000000000000 : Rat) + (1775307897026742196701 / 163840000000000000000000000 : Rat) = (4921999878998583033741 / 204800000000000000000000000 : Rat))
  have hreplay022 :
      Shard029.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1359986419904848402293 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard029.root_eq_path] using Shard029.replay
  have hreplay023 :
      Shard030.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2181994990422874857351 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard030.root_eq_path] using Shard030.replay
  have hraw024 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (1359986419904848402293 / 163840000000000000000000000 : Rat) + (2181994990422874857351 / 204800000000000000000000000 : Rat) = (15527912061215741440869 / 819200000000000000000000000 : Rat))
  have hreplay025 :
      Shard031.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (6857950900678326511821 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard031.root_eq_path] using Shard031.replay
  have hreplay026 :
      Shard032.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (8400576407705535023883 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard032.root_eq_path] using Shard032.replay
  have hraw027 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (6857950900678326511821 / 819200000000000000000000000 : Rat) + (8400576407705535023883 / 819200000000000000000000000 : Rat) = (1907315913547982691963 / 102400000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (15527912061215741440869 / 819200000000000000000000000 : Rat) + (1907315913547982691963 / 102400000000000000000000000 : Rat) = (30786439369599602976573 / 819200000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (4921999878998583033741 / 204800000000000000000000000 : Rat) + (30786439369599602976573 / 819200000000000000000000000 : Rat) = (50474438885593935111537 / 819200000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (13600872643065145172163 / 204800000000000000000000000 : Rat) + (50474438885593935111537 / 819200000000000000000000000 : Rat) = (104877929457854515800189 / 819200000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch000
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
