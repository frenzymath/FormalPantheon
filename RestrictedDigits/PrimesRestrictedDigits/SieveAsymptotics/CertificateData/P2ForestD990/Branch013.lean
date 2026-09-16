import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard224
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard225
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard226
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard227
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard228
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard229
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard230
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard231
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard232
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard233
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard234
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard235
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard236
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard237
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard238

/-!
# exact P2 forest branch Branch013
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch013

/- Root 1, exact path ((1, 'left'), (3, 'right'), (4, 'right'), (3, 'right')), 365 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            Shard224.tree
            Shard225.tree
          )
          (.split (0 : Fin 6)
            Shard226.tree
            Shard227.tree
          )
        )
        (.split (0 : Fin 6)
          (.split (3 : Fin 6)
            Shard228.tree
            Shard229.tree
          )
          Shard230.tree
        )
      )
      (.split (0 : Fin 6)
        Shard231.tree
        (.split (1 : Fin 6)
          Shard232.tree
          (.split (0 : Fin 6)
            Shard233.tree
            Shard234.tree
          )
        )
      )
    )
    (.split (0 : Fin 6)
      Shard235.tree
      (.split (0 : Fin 6)
        Shard236.tree
        (.split (2 : Fin 6)
          Shard237.tree
          Shard238.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard224.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard224.root_eq_path] using Shard224.valid
  have hvalid001 :
      Shard225.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard225.root_eq_path] using Shard225.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard226.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard226.root_eq_path] using Shard226.valid
  have hvalid004 :
      Shard227.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard227.root_eq_path] using Shard227.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard228.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard228.root_eq_path] using Shard228.valid
  have hvalid008 :
      Shard229.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard229.root_eq_path] using Shard229.valid
  have hvalid009 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard230.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard230.root_eq_path] using Shard230.valid
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid009 hvalid010
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard231.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard231.root_eq_path] using Shard231.valid
  have hvalid014 :
      Shard232.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard232.root_eq_path] using Shard232.valid
  have hvalid015 :
      Shard233.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard233.root_eq_path] using Shard233.valid
  have hvalid016 :
      Shard234.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard234.root_eq_path] using Shard234.valid
  have hvalid017 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid014 hvalid017
  have hvalid019 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hvalid013 hvalid018
  have hvalid020 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid012 hvalid019
  have hvalid021 :
      Shard235.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard235.root_eq_path] using Shard235.valid
  have hvalid022 :
      Shard236.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard236.root_eq_path] using Shard236.valid
  have hvalid023 :
      Shard237.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard237.root_eq_path] using Shard237.valid
  have hvalid024 :
      Shard238.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard238.root_eq_path] using Shard238.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid021 hvalid026
  have hvalid028 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid020 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
      (7853390487429774676711749 / 32768000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard224.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (4501008825127105192047 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard224.root_eq_path] using Shard224.replay
  have hreplay001 :
      Shard225.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (47305175298013661754771 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard225.root_eq_path] using Shard225.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (4501008825127105192047 / 2048000000000000000000000000 : Rat) + (47305175298013661754771 / 8192000000000000000000000000 : Rat) = (65309210598522082522959 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard226.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (11040551140694038178427 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard226.root_eq_path] using Shard226.replay
  have hreplay004 :
      Shard227.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (225223634050245033631983 / 32768000000000000000000000000 : Rat) := by
    simpa only [Shard227.root_eq_path] using Shard227.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (11040551140694038178427 / 3276800000000000000000000000 : Rat) + (225223634050245033631983 / 32768000000000000000000000000 : Rat) = (335629145457185415416253 / 32768000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (65309210598522082522959 / 8192000000000000000000000000 : Rat) + (335629145457185415416253 / 32768000000000000000000000000 : Rat) = (596865987851273745508089 / 32768000000000000000000000000 : Rat))
  have hreplay007 :
      Shard228.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (30772660564328762144061 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard228.root_eq_path] using Shard228.replay
  have hreplay008 :
      Shard229.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (4836587216785489376919 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard229.root_eq_path] using Shard229.replay
  have hraw009 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (30772660564328762144061 / 8192000000000000000000000000 : Rat) + (4836587216785489376919 / 1638400000000000000000000000 : Rat) = (3434724790516013064291 / 512000000000000000000000000 : Rat))
  have hreplay010 :
      Shard230.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (223431711627699864672849 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard230.root_eq_path] using Shard230.replay
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay009 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (3434724790516013064291 / 512000000000000000000000000 : Rat) + (223431711627699864672849 / 16384000000000000000000000000 : Rat) = (333342904924212282730161 / 16384000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (596865987851273745508089 / 32768000000000000000000000000 : Rat) + (333342904924212282730161 / 16384000000000000000000000000 : Rat) = (1263551797699698310968411 / 32768000000000000000000000000 : Rat))
  have hreplay013 :
      Shard231.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (394447898438291619844281 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard231.root_eq_path] using Shard231.replay
  have hreplay014 :
      Shard232.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (298280638914732796770621 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard232.root_eq_path] using Shard232.replay
  have hreplay015 :
      Shard233.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (9576171590142289222809 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard233.root_eq_path] using Shard233.replay
  have hreplay016 :
      Shard234.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (44515654620413973479217 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard234.root_eq_path] using Shard234.replay
  have hraw017 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (9576171590142289222809 / 1024000000000000000000000000 : Rat) + (44515654620413973479217 / 4096000000000000000000000000 : Rat) = (82820340980983130370453 / 4096000000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay014 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (298280638914732796770621 / 16384000000000000000000000000 : Rat) + (82820340980983130370453 / 4096000000000000000000000000 : Rat) = (629562002838665318252433 / 16384000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hreplay013 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (394447898438291619844281 / 16384000000000000000000000000 : Rat) + (629562002838665318252433 / 16384000000000000000000000000 : Rat) = (512004950638478469048357 / 8192000000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay012 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (1263551797699698310968411 / 32768000000000000000000000000 : Rat) + (512004950638478469048357 / 8192000000000000000000000000 : Rat) = (3311571600253612187161839 / 32768000000000000000000000000 : Rat))
  have hreplay021 :
      Shard235.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (117928483385627545580871 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard235.root_eq_path] using Shard235.replay
  have hreplay022 :
      Shard236.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (127374485064198693410997 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard236.root_eq_path] using Shard236.replay
  have hreplay023 :
      Shard237.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (143996806871522053239717 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard237.root_eq_path] using Shard237.replay
  have hreplay024 :
      Shard238.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (12581735544969478331049 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard238.root_eq_path] using Shard238.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (143996806871522053239717 / 8192000000000000000000000000 : Rat) + (12581735544969478331049 / 512000000000000000000000000 : Rat) = (345304575591033706536501 / 8192000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (127374485064198693410997 / 3276800000000000000000000000 : Rat) + (345304575591033706536501 / 8192000000000000000000000000 : Rat) = (1327481576503060880127987 / 16384000000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay021 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (117928483385627545580871 / 2048000000000000000000000000 : Rat) + (1327481576503060880127987 / 16384000000000000000000000000 : Rat) = (454181888717616248954991 / 3276800000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay020 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (3311571600253612187161839 / 32768000000000000000000000000 : Rat) + (454181888717616248954991 / 3276800000000000000000000000 : Rat) = (7853390487429774676711749 / 32768000000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch013
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
