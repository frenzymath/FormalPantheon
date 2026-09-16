import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard176
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard177
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard178
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard179
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard180
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard181
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard182
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard183
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard184
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard185
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard186
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard187
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard188
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard189
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard190
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard191

/-!
# exact P2 forest branch Branch010
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch010

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'left'), (2, 'left')), 366 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard176.tree
          Shard177.tree
        )
        (.split (2 : Fin 6)
          Shard178.tree
          Shard179.tree
        )
      )
      (.split (3 : Fin 6)
        Shard180.tree
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            Shard181.tree
            Shard182.tree
          )
          Shard183.tree
        )
      )
    )
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        Shard184.tree
        (.split (0 : Fin 6)
          Shard185.tree
          Shard186.tree
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard187.tree
          (.split (1 : Fin 6)
            Shard188.tree
            Shard189.tree
          )
        )
        (.split (0 : Fin 6)
          Shard190.tree
          Shard191.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
  have hvalid000 :
      Shard176.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard176.root_eq_path] using Shard176.valid
  have hvalid001 :
      Shard177.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard177.root_eq_path] using Shard177.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard178.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard178.root_eq_path] using Shard178.valid
  have hvalid004 :
      Shard179.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard179.root_eq_path] using Shard179.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard180.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard180.root_eq_path] using Shard180.valid
  have hvalid008 :
      Shard181.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard181.root_eq_path] using Shard181.valid
  have hvalid009 :
      Shard182.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard182.root_eq_path] using Shard182.valid
  have hvalid010 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :
      Shard183.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard183.root_eq_path] using Shard183.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard184.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard184.root_eq_path] using Shard184.valid
  have hvalid016 :
      Shard185.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard185.root_eq_path] using Shard185.valid
  have hvalid017 :
      Shard186.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard186.root_eq_path] using Shard186.valid
  have hvalid018 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard187.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard187.root_eq_path] using Shard187.valid
  have hvalid021 :
      Shard188.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard188.root_eq_path] using Shard188.valid
  have hvalid022 :
      Shard189.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard189.root_eq_path] using Shard189.valid
  have hvalid023 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid020 hvalid023
  have hvalid025 :
      Shard190.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard190.root_eq_path] using Shard190.valid
  have hvalid026 :
      Shard191.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard191.root_eq_path] using Shard191.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid019 hvalid028
  have hvalid030 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
      (1482554046486268268241489 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard176.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (3189573891802669179447 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard176.root_eq_path] using Shard176.replay
  have hreplay001 :
      Shard177.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (12670970577719813552871 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard177.root_eq_path] using Shard177.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (3189573891802669179447 / 2048000000000000000000000000 : Rat) + (12670970577719813552871 / 4096000000000000000000000000 : Rat) = (3810023672265030382353 / 819200000000000000000000000 : Rat))
  have hreplay003 :
      Shard178.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (27990067314544040626011 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard178.root_eq_path] using Shard178.replay
  have hreplay004 :
      Shard179.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (17535608731862441485749 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard179.root_eq_path] using Shard179.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (27990067314544040626011 / 8192000000000000000000000000 : Rat) + (17535608731862441485749 / 4096000000000000000000000000 : Rat) = (63061284778268923597509 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (3810023672265030382353 / 819200000000000000000000000 : Rat) + (63061284778268923597509 / 8192000000000000000000000000 : Rat) = (101161521500919227421039 / 8192000000000000000000000000 : Rat))
  have hreplay007 :
      Shard180.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (26158303681929476777457 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard180.root_eq_path] using Shard180.replay
  have hreplay008 :
      Shard181.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (18390600069084421442649 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard181.root_eq_path] using Shard181.replay
  have hreplay009 :
      Shard182.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (25716950897014793700549 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard182.root_eq_path] using Shard182.replay
  have hraw010 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (18390600069084421442649 / 16384000000000000000000000000 : Rat) + (25716950897014793700549 / 16384000000000000000000000000 : Rat) = (22053775483049607571599 / 8192000000000000000000000000 : Rat))
  have hreplay011 :
      Shard183.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (50778712646824984047063 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard183.root_eq_path] using Shard183.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (22053775483049607571599 / 8192000000000000000000000000 : Rat) + (50778712646824984047063 / 16384000000000000000000000000 : Rat) = (94886263612924199190261 / 16384000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (26158303681929476777457 / 3276800000000000000000000000 : Rat) + (94886263612924199190261 / 16384000000000000000000000000 : Rat) = (112838891011285791538773 / 8192000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (101161521500919227421039 / 8192000000000000000000000000 : Rat) + (112838891011285791538773 / 8192000000000000000000000000 : Rat) = (53500103128051254739953 / 2048000000000000000000000000 : Rat))
  have hreplay015 :
      Shard184.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1701126304136890981749 / 128000000000000000000000000 : Rat) := by
    simpa only [Shard184.root_eq_path] using Shard184.replay
  have hreplay016 :
      Shard185.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (4413832994890899343161 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard185.root_eq_path] using Shard185.replay
  have hreplay017 :
      Shard186.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (52172331209735812967583 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard186.root_eq_path] using Shard186.replay
  have hraw018 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (4413832994890899343161 / 819200000000000000000000000 : Rat) + (52172331209735812967583 / 8192000000000000000000000000 : Rat) = (96310661158644806399193 / 8192000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (1701126304136890981749 / 128000000000000000000000000 : Rat) + (96310661158644806399193 / 8192000000000000000000000000 : Rat) = (205182744623405829231129 / 8192000000000000000000000000 : Rat))
  have hreplay020 :
      Shard187.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (171037101162597690309093 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard187.root_eq_path] using Shard187.replay
  have hreplay021 :
      Shard188.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (115155887287342453995411 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard188.root_eq_path] using Shard188.replay
  have hreplay022 :
      Shard189.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (3878406159830017478037 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard189.root_eq_path] using Shard189.replay
  have hraw023 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (115155887287342453995411 / 16384000000000000000000000000 : Rat) + (3878406159830017478037 / 655360000000000000000000000 : Rat) = (6628626290096652842073 / 512000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay020 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (171037101162597690309093 / 16384000000000000000000000000 : Rat) + (6628626290096652842073 / 512000000000000000000000000 : Rat) = (383153142445690581255429 / 16384000000000000000000000000 : Rat))
  have hreplay025 :
      Shard190.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (61606721525316037898481 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard190.root_eq_path] using Shard190.replay
  have hreplay026 :
      Shard191.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (8613821669920244675451 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard191.root_eq_path] using Shard191.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (61606721525316037898481 / 8192000000000000000000000000 : Rat) + (8613821669920244675451 / 1024000000000000000000000000 : Rat) = (130517294884677995302089 / 8192000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (383153142445690581255429 / 16384000000000000000000000000 : Rat) + (130517294884677995302089 / 8192000000000000000000000000 : Rat) = (644187732215046571859607 / 16384000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay019 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (205182744623405829231129 / 8192000000000000000000000000 : Rat) + (644187732215046571859607 / 16384000000000000000000000000 : Rat) = (210910644292371646064373 / 3276800000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (53500103128051254739953 / 2048000000000000000000000000 : Rat) + (210910644292371646064373 / 3276800000000000000000000000 : Rat) = (1482554046486268268241489 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch010
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
