import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard353
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard354
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard355
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard356
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard357
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard358
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard359
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard360
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard361
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard362
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard363
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard364
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard365
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard366
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard367
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard368

/-!
# exact P2 forest branch Branch022
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch022

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'right'), (1, 'left')), 318 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard353.tree
          Shard354.tree
        )
        (.split (2 : Fin 6)
          Shard355.tree
          Shard356.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard357.tree
          Shard358.tree
        )
        (.split (2 : Fin 6)
          Shard359.tree
          Shard360.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard361.tree
          Shard362.tree
        )
        (.split (2 : Fin 6)
          Shard363.tree
          Shard364.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          Shard365.tree
          Shard366.tree
        )
        (.split (4 : Fin 6)
          Shard367.tree
          Shard368.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard353.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard353.root_eq_path] using Shard353.valid
  have hvalid001 :
      Shard354.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard354.root_eq_path] using Shard354.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard355.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard355.root_eq_path] using Shard355.valid
  have hvalid004 :
      Shard356.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard356.root_eq_path] using Shard356.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard357.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard357.root_eq_path] using Shard357.valid
  have hvalid008 :
      Shard358.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard358.root_eq_path] using Shard358.valid
  have hvalid009 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard359.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard359.root_eq_path] using Shard359.valid
  have hvalid011 :
      Shard360.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard360.root_eq_path] using Shard360.valid
  have hvalid012 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard361.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard361.root_eq_path] using Shard361.valid
  have hvalid016 :
      Shard362.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard362.root_eq_path] using Shard362.valid
  have hvalid017 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard363.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard363.root_eq_path] using Shard363.valid
  have hvalid019 :
      Shard364.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard364.root_eq_path] using Shard364.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard365.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard365.root_eq_path] using Shard365.valid
  have hvalid023 :
      Shard366.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard366.root_eq_path] using Shard366.valid
  have hvalid024 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard367.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard367.root_eq_path] using Shard367.valid
  have hvalid026 :
      Shard368.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard368.root_eq_path] using Shard368.valid
  have hvalid027 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
      (6531118995960691932611943 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard353.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (214930643667636965846409 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard353.root_eq_path] using Shard353.replay
  have hreplay001 :
      Shard354.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (254696018267018797742853 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard354.root_eq_path] using Shard354.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (214930643667636965846409 / 8192000000000000000000000000 : Rat) + (254696018267018797742853 / 8192000000000000000000000000 : Rat) = (234813330967327881794631 / 4096000000000000000000000000 : Rat))
  have hreplay003 :
      Shard355.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (200734981191914454021033 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard355.root_eq_path] using Shard355.replay
  have hreplay004 :
      Shard356.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (234858266833482743529033 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard356.root_eq_path] using Shard356.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (200734981191914454021033 / 8192000000000000000000000000 : Rat) + (234858266833482743529033 / 8192000000000000000000000000 : Rat) = (217796624012698598775033 / 4096000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (234813330967327881794631 / 4096000000000000000000000000 : Rat) + (217796624012698598775033 / 4096000000000000000000000000 : Rat) = (7072030546562913758901 / 64000000000000000000000000 : Rat))
  have hreplay007 :
      Shard357.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (3641584877387140758921 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard357.root_eq_path] using Shard357.replay
  have hreplay008 :
      Shard358.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (2716629893690492172141 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard358.root_eq_path] using Shard358.replay
  have hraw009 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (3641584877387140758921 / 163840000000000000000000000 : Rat) + (2716629893690492172141 / 102400000000000000000000000 : Rat) = (39940963536459641171733 / 819200000000000000000000000 : Rat))
  have hreplay010 :
      Shard359.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (222352352005861723665897 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard359.root_eq_path] using Shard359.replay
  have hreplay011 :
      Shard360.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (12012544007489087948601 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard360.root_eq_path] using Shard360.replay
  have hraw012 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (222352352005861723665897 / 8192000000000000000000000000 : Rat) + (12012544007489087948601 / 409600000000000000000000000 : Rat) = (462603232155643482637917 / 8192000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (39940963536459641171733 / 819200000000000000000000000 : Rat) + (462603232155643482637917 / 8192000000000000000000000000 : Rat) = (862012867520239894355247 / 8192000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (7072030546562913758901 / 64000000000000000000000000 : Rat) + (862012867520239894355247 / 8192000000000000000000000000 : Rat) = (70689311099211714219783 / 327680000000000000000000000 : Rat))
  have hreplay015 :
      Shard361.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (156353450969460391660143 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard361.root_eq_path] using Shard361.replay
  have hreplay016 :
      Shard362.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (179425964060461765201257 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard362.root_eq_path] using Shard362.replay
  have hraw017 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (156353450969460391660143 / 8192000000000000000000000000 : Rat) + (179425964060461765201257 / 8192000000000000000000000000 : Rat) = (1678897075149610784307 / 40960000000000000000000000 : Rat))
  have hreplay018 :
      Shard363.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (189715365066330743846337 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard363.root_eq_path] using Shard363.replay
  have hreplay019 :
      Shard364.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (206381299649515178867793 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard364.root_eq_path] using Shard364.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (189715365066330743846337 / 8192000000000000000000000000 : Rat) + (206381299649515178867793 / 8192000000000000000000000000 : Rat) = (39609666471584592271413 / 819200000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (1678897075149610784307 / 40960000000000000000000000 : Rat) + (39609666471584592271413 / 819200000000000000000000000 : Rat) = (73187607974576807957553 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard365.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (46485715480262011403829 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard365.root_eq_path] using Shard365.replay
  have hreplay023 :
      Shard366.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (13400984764099206549423 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard366.root_eq_path] using Shard366.replay
  have hraw024 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (46485715480262011403829 / 2048000000000000000000000000 : Rat) + (13400984764099206549423 / 512000000000000000000000000 : Rat) = (100089654536658837601521 / 2048000000000000000000000000 : Rat))
  have hreplay025 :
      Shard367.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (360971121404605264665939 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard367.root_eq_path] using Shard367.replay
  have hreplay026 :
      Shard368.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (185606461905347048496813 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard368.root_eq_path] using Shard368.replay
  have hraw027 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (360971121404605264665939 / 16384000000000000000000000000 : Rat) + (185606461905347048496813 / 8192000000000000000000000000 : Rat) = (146436809043059872331913 / 3276800000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (100089654536658837601521 / 2048000000000000000000000000 : Rat) + (146436809043059872331913 / 3276800000000000000000000000 : Rat) = (1532901281508570062471733 / 16384000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (73187607974576807957553 / 819200000000000000000000000 : Rat) + (1532901281508570062471733 / 16384000000000000000000000000 : Rat) = (2996653441000106221622793 / 16384000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (70689311099211714219783 / 327680000000000000000000000 : Rat) + (2996653441000106221622793 / 16384000000000000000000000000 : Rat) = (6531118995960691932611943 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch022
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
