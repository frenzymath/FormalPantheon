import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard147
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard148
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard149
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard150
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard151
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard152
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard153
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard154
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard155
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard156
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard157
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard158
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard159
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard160

/-!
# exact P2 forest branch Branch008
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch008

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'right'), (2, 'left')), 317 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard147.tree
          Shard148.tree
        )
        (.split (1 : Fin 6)
          Shard149.tree
          Shard150.tree
        )
      )
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard151.tree
          Shard152.tree
        )
        (.split (3 : Fin 6)
          Shard153.tree
          Shard154.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        Shard155.tree
        Shard156.tree
      )
      (.split (3 : Fin 6)
        (.split (0 : Fin 6)
          Shard157.tree
          Shard158.tree
        )
        (.split (0 : Fin 6)
          Shard159.tree
          Shard160.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
  have hvalid000 :
      Shard147.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard147.root_eq_path] using Shard147.valid
  have hvalid001 :
      Shard148.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard148.root_eq_path] using Shard148.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard149.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard149.root_eq_path] using Shard149.valid
  have hvalid004 :
      Shard150.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard150.root_eq_path] using Shard150.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard151.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard151.root_eq_path] using Shard151.valid
  have hvalid008 :
      Shard152.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard152.root_eq_path] using Shard152.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard153.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard153.root_eq_path] using Shard153.valid
  have hvalid011 :
      Shard154.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard154.root_eq_path] using Shard154.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard155.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard155.root_eq_path] using Shard155.valid
  have hvalid016 :
      Shard156.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard156.root_eq_path] using Shard156.valid
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard157.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard157.root_eq_path] using Shard157.valid
  have hvalid019 :
      Shard158.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard158.root_eq_path] using Shard158.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard159.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard159.root_eq_path] using Shard159.valid
  have hvalid022 :
      Shard160.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard160.root_eq_path] using Shard160.valid
  have hvalid023 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid020 hvalid023
  have hvalid025 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid024
  have hvalid026 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid014 hvalid025
  simpa only [tree] using hvalid026

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
      (2605771117477186669109277 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard147.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (14805106650261644889303 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard147.root_eq_path] using Shard147.replay
  have hreplay001 :
      Shard148.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (42342337364113595237427 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard148.root_eq_path] using Shard148.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (14805106650261644889303 / 4096000000000000000000000000 : Rat) + (42342337364113595237427 / 8192000000000000000000000000 : Rat) = (71952550664636885016033 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard149.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (25686382789853309356353 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard149.root_eq_path] using Shard149.replay
  have hreplay004 :
      Shard150.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (23222376888603843579651 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard150.root_eq_path] using Shard150.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (25686382789853309356353 / 4096000000000000000000000000 : Rat) + (23222376888603843579651 / 4096000000000000000000000000 : Rat) = (12227189919614288234001 / 1024000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (71952550664636885016033 / 8192000000000000000000000000 : Rat) + (12227189919614288234001 / 1024000000000000000000000000 : Rat) = (169770070021551190888041 / 8192000000000000000000000000 : Rat))
  have hreplay007 :
      Shard151.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (36276654784865998822209 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard151.root_eq_path] using Shard151.replay
  have hreplay008 :
      Shard152.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (68738634154285347588669 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard152.root_eq_path] using Shard152.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (36276654784865998822209 / 4096000000000000000000000000 : Rat) + (68738634154285347588669 / 8192000000000000000000000000 : Rat) = (141291943724017345233087 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard153.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (26427393035936950581027 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard153.root_eq_path] using Shard153.replay
  have hreplay011 :
      Shard154.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (39247440986710508052339 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard154.root_eq_path] using Shard154.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (26427393035936950581027 / 2048000000000000000000000000 : Rat) + (39247440986710508052339 / 4096000000000000000000000000 : Rat) = (92102227058584409214393 / 4096000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (141291943724017345233087 / 8192000000000000000000000000 : Rat) + (92102227058584409214393 / 4096000000000000000000000000 : Rat) = (325496397841186163661873 / 8192000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (169770070021551190888041 / 8192000000000000000000000000 : Rat) + (325496397841186163661873 / 8192000000000000000000000000 : Rat) = (247633233931368677274957 / 4096000000000000000000000000 : Rat))
  have hreplay015 :
      Shard155.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (161528336217585326389941 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard155.root_eq_path] using Shard155.replay
  have hreplay016 :
      Shard156.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (183462709559034589307883 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard156.root_eq_path] using Shard156.replay
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (161528336217585326389941 / 8192000000000000000000000000 : Rat) + (183462709559034589307883 / 8192000000000000000000000000 : Rat) = (10780970180519372365557 / 256000000000000000000000000 : Rat))
  have hreplay018 :
      Shard157.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (259650457310034700181541 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard157.root_eq_path] using Shard157.replay
  have hreplay019 :
      Shard158.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (202439646067616633651283 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard158.root_eq_path] using Shard158.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (259650457310034700181541 / 16384000000000000000000000000 : Rat) + (202439646067616633651283 / 16384000000000000000000000000 : Rat) = (57761262922206416729103 / 2048000000000000000000000000 : Rat))
  have hreplay021 :
      Shard159.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (10589040334734993210627 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard159.root_eq_path] using Shard159.replay
  have hreplay022 :
      Shard160.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (99219989226222982257651 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard160.root_eq_path] using Shard160.replay
  have hraw023 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (10589040334734993210627 / 655360000000000000000000000 : Rat) + (99219989226222982257651 / 8192000000000000000000000000 : Rat) = (463165986820820794780977 / 16384000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay020 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (57761262922206416729103 / 2048000000000000000000000000 : Rat) + (463165986820820794780977 / 16384000000000000000000000000 : Rat) = (925256090198472128613801 / 16384000000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (10780970180519372365557 / 256000000000000000000000000 : Rat) + (925256090198472128613801 / 16384000000000000000000000000 : Rat) = (1615238181751711960009449 / 16384000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay014 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (247633233931368677274957 / 4096000000000000000000000000 : Rat) + (1615238181751711960009449 / 16384000000000000000000000000 : Rat) = (2605771117477186669109277 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay026

end Branch008
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
