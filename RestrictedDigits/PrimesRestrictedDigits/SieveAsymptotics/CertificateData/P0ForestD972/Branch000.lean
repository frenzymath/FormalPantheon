import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard002
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard003
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard005
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard007
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard008
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard009
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard011
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard012
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard013
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard014

/-!
# exact P0 forest branch Branch000
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch000

/- Root 0, exact path ((1, 'left'),), 1481 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (1 : Fin 6)
    (.split (1 : Fin 6)
      (.split (0 : Fin 6)
        Shard000.tree
        Shard001.tree
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          Shard002.tree
          Shard003.tree
        )
        (.split (2 : Fin 6)
          Shard004.tree
          Shard005.tree
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (2 : Fin 6)
          Shard006.tree
          Shard007.tree
        )
        (.split (0 : Fin 6)
          Shard008.tree
          Shard009.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard010.tree
          Shard011.tree
        )
        (.split (1 : Fin 6)
          Shard012.tree
          (.split (0 : Fin 6)
            Shard013.tree
            Shard014.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard000.tree.coverValid sectionSixP0LeafValidD970 (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard000.root_eq_path] using Shard000.valid
  have hvalid001 :
      Shard001.tree.coverValid sectionSixP0LeafValidD970 (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard001.root_eq_path] using Shard001.valid
  have hvalid002 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard002.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard002.root_eq_path] using Shard002.valid
  have hvalid004 :
      Shard003.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard003.root_eq_path] using Shard003.valid
  have hvalid005 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :
      Shard004.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard004.root_eq_path] using Shard004.valid
  have hvalid007 :
      Shard005.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard005.root_eq_path] using Shard005.valid
  have hvalid008 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid009
  have hvalid011 :
      Shard006.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard006.root_eq_path] using Shard006.valid
  have hvalid012 :
      Shard007.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard007.root_eq_path] using Shard007.valid
  have hvalid013 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard008.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard008.root_eq_path] using Shard008.valid
  have hvalid015 :
      Shard009.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard009.root_eq_path] using Shard009.valid
  have hvalid016 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :
      Shard010.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard010.root_eq_path] using Shard010.valid
  have hvalid019 :
      Shard011.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard011.root_eq_path] using Shard011.valid
  have hvalid020 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard012.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard012.root_eq_path] using Shard012.valid
  have hvalid022 :
      Shard013.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard013.root_eq_path] using Shard013.valid
  have hvalid023 :
      Shard014.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard014.root_eq_path] using Shard014.valid
  have hvalid024 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid024
  have hvalid026 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid020 hvalid025
  have hvalid027 :=
    valid_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid017 hvalid026
  have hvalid028 :=
    valid_split (T := (sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid010 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) (fun _ q => q) =
      (12198317535309807058017951 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard000.tree.replayWeightRat (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (409159573385379245640467 / 2457600000000000000000000000 : Rat) := by
    simpa only [Shard000.root_eq_path] using Shard000.replay
  have hreplay001 :
      Shard001.tree.replayWeightRat (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (790290264622576324642057 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard001.root_eq_path] using Shard001.replay
  have hraw002 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (409159573385379245640467 / 2457600000000000000000000000 : Rat) + (790290264622576324642057 / 1638400000000000000000000000 : Rat) = (637837988127697493041421 / 983040000000000000000000000 : Rat))
  have hreplay003 :
      Shard002.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (448784763633777693057043 / 1228800000000000000000000000 : Rat) := by
    simpa only [Shard002.root_eq_path] using Shard002.replay
  have hreplay004 :
      Shard003.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ q => q) =
        (1110466283383469761191373 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard003.root_eq_path] using Shard003.replay
  have hraw005 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (448784763633777693057043 / 1228800000000000000000000000 : Rat) + (1110466283383469761191373 / 4915200000000000000000000000 : Rat) = (581121067583716106683909 / 983040000000000000000000000 : Rat))
  have hreplay006 :
      Shard004.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (2055525096153004360053113 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard004.root_eq_path] using Shard004.replay
  have hreplay007 :
      Shard005.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (525086761485081617151893 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard005.root_eq_path] using Shard005.replay
  have hraw008 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (2055525096153004360053113 / 4915200000000000000000000000 : Rat) + (525086761485081617151893 / 819200000000000000000000000 : Rat) = (5206045665063494062964471 / 4915200000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (581121067583716106683909 / 983040000000000000000000000 : Rat) + (5206045665063494062964471 / 4915200000000000000000000000 : Rat) = (506978187686379662274001 / 307200000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (637837988127697493041421 / 983040000000000000000000000 : Rat) + (506978187686379662274001 / 307200000000000000000000000 : Rat) = (11300840943620562061591121 / 4915200000000000000000000000 : Rat))
  have hreplay011 :
      Shard006.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (4976814683672239019728271 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard006.root_eq_path] using Shard006.replay
  have hreplay012 :
      Shard007.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (68118340686039786567911 / 98304000000000000000000000 : Rat) := by
    simpa only [Shard007.root_eq_path] using Shard007.replay
  have hraw013 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (4976814683672239019728271 / 9830400000000000000000000000 : Rat) + (68118340686039786567911 / 98304000000000000000000000 : Rat) = (11788648752276217676519371 / 9830400000000000000000000000 : Rat))
  have hreplay014 :
      Shard008.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (470581554627823954789659 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard008.root_eq_path] using Shard008.replay
  have hreplay015 :
      Shard009.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (823145140953565522060011 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard009.root_eq_path] using Shard009.replay
  have hraw016 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (470581554627823954789659 / 1638400000000000000000000000 : Rat) + (823145140953565522060011 / 1638400000000000000000000000 : Rat) = (129372669558138947684967 / 163840000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (11788648752276217676519371 / 9830400000000000000000000000 : Rat) + (129372669558138947684967 / 163840000000000000000000000 : Rat) = (19551008925764554537617391 / 9830400000000000000000000000 : Rat))
  have hreplay018 :
      Shard010.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ q => q) =
        (2857787162653472868957367 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard010.root_eq_path] using Shard010.replay
  have hreplay019 :
      Shard011.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ q => q) =
        (613036564049190209154621 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard011.root_eq_path] using Shard011.replay
  have hraw020 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (2857787162653472868957367 / 4915200000000000000000000000 : Rat) + (613036564049190209154621 / 819200000000000000000000000 : Rat) = (6536006546948614123885093 / 4915200000000000000000000000 : Rat))
  have hreplay021 :
      Shard012.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (2163739526150763359956027 / 2457600000000000000000000000 : Rat) := by
    simpa only [Shard012.root_eq_path] using Shard012.replay
  have hreplay022 :
      Shard013.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (2234799406789408846343833 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard013.root_eq_path] using Shard013.replay
  have hreplay023 :
      Shard014.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (4840644386774064307026113 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard014.root_eq_path] using Shard014.replay
  have hraw024 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (2234799406789408846343833 / 4915200000000000000000000000 : Rat) + (4840644386774064307026113 / 9830400000000000000000000000 : Rat) = (9310243200352881999713779 / 9830400000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (2163739526150763359956027 / 2457600000000000000000000000 : Rat) + (9310243200352881999713779 / 9830400000000000000000000000 : Rat) = (17965201304955935439537887 / 9830400000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay020 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (6536006546948614123885093 / 4915200000000000000000000000 : Rat) + (17965201304955935439537887 / 9830400000000000000000000000 : Rat) = (31037214398853163687308073 / 9830400000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay017 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (19551008925764554537617391 / 9830400000000000000000000000 : Rat) + (31037214398853163687308073 / 9830400000000000000000000000 : Rat) = (6323527915577214778115683 / 1228800000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (sectionSixP0RootD971 (0 : Fin 3)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay010 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (11300840943620562061591121 / 4915200000000000000000000000 : Rat) + (6323527915577214778115683 / 1228800000000000000000000000 : Rat) = (12198317535309807058017951 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch000
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
