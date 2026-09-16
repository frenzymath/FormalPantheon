import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard340
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard341
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard342
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard343
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard344
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard345
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard346
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard347
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard348
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard349
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard350
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard351
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard352

/-!
# exact P2 forest branch Branch021
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch021

/- Root 2, exact path ((2, 'left'), (4, 'left'), (5, 'left'), (2, 'left'), (4, 'right')), 310 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (4 : Fin 6)
          Shard340.tree
          Shard341.tree
        )
        (.split (4 : Fin 6)
          Shard342.tree
          Shard343.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard344.tree
          Shard345.tree
        )
        (.split (0 : Fin 6)
          Shard346.tree
          Shard347.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        Shard348.tree
        Shard349.tree
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          Shard350.tree
          Shard351.tree
        )
        Shard352.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard340.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard340.root_eq_path] using Shard340.valid
  have hvalid001 :
      Shard341.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard341.root_eq_path] using Shard341.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard342.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard342.root_eq_path] using Shard342.valid
  have hvalid004 :
      Shard343.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard343.root_eq_path] using Shard343.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard344.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard344.root_eq_path] using Shard344.valid
  have hvalid008 :
      Shard345.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard345.root_eq_path] using Shard345.valid
  have hvalid009 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard346.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard346.root_eq_path] using Shard346.valid
  have hvalid011 :
      Shard347.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard347.root_eq_path] using Shard347.valid
  have hvalid012 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard348.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard348.root_eq_path] using Shard348.valid
  have hvalid016 :
      Shard349.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard349.root_eq_path] using Shard349.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard350.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard350.root_eq_path] using Shard350.valid
  have hvalid019 :
      Shard351.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard351.root_eq_path] using Shard351.valid
  have hvalid020 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :
      Shard352.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard352.root_eq_path] using Shard352.valid
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid022
  have hvalid024 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid023
  simpa only [tree] using hvalid024

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (2732325459424190545353039 / 8192000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard340.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (198881675458109892755847 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard340.root_eq_path] using Shard340.replay
  have hreplay001 :
      Shard341.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (466283895500289812492709 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard341.root_eq_path] using Shard341.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (198881675458109892755847 / 8192000000000000000000000000 : Rat) + (466283895500289812492709 / 16384000000000000000000000000 : Rat) = (864047246416509598004403 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard342.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (32330850807792940841853 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard342.root_eq_path] using Shard342.replay
  have hreplay004 :
      Shard343.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (3875884808730818560479 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard343.root_eq_path] using Shard343.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (32330850807792940841853 / 1638400000000000000000000000 : Rat) + (3875884808730818560479 / 163840000000000000000000000 : Rat) = (71089698895101126446643 / 1638400000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (864047246416509598004403 / 16384000000000000000000000000 : Rat) + (71089698895101126446643 / 1638400000000000000000000000 : Rat) = (1574944235367520862470833 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Shard344.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (150801165410073940115037 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard344.root_eq_path] using Shard344.replay
  have hreplay008 :
      Shard345.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (91516044339207925741863 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard345.root_eq_path] using Shard345.replay
  have hraw009 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (150801165410073940115037 / 8192000000000000000000000000 : Rat) + (91516044339207925741863 / 4096000000000000000000000000 : Rat) = (333833254088489791598763 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard346.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (204343776644546870247141 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard346.root_eq_path] using Shard346.replay
  have hreplay011 :
      Shard347.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (180754932886392879524943 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard347.root_eq_path] using Shard347.replay
  have hraw012 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (204343776644546870247141 / 8192000000000000000000000000 : Rat) + (180754932886392879524943 / 8192000000000000000000000000 : Rat) = (96274677382734937443021 / 2048000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (333833254088489791598763 / 8192000000000000000000000000 : Rat) + (96274677382734937443021 / 2048000000000000000000000000 : Rat) = (718931963619429541370847 / 8192000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (1574944235367520862470833 / 16384000000000000000000000000 : Rat) + (718931963619429541370847 / 8192000000000000000000000000 : Rat) = (3012808162606379945212527 / 16384000000000000000000000000 : Rat))
  have hreplay015 :
      Shard348.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (136778595284401133295249 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard348.root_eq_path] using Shard348.replay
  have hreplay016 :
      Shard349.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (160889702605917211573101 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard349.root_eq_path] using Shard349.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (136778595284401133295249 / 4096000000000000000000000000 : Rat) + (160889702605917211573101 / 4096000000000000000000000000 : Rat) = (5953365957806366897367 / 81920000000000000000000000 : Rat))
  have hreplay018 :
      Shard350.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (5321766381998068515969 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard350.root_eq_path] using Shard350.replay
  have hreplay019 :
      Shard351.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (304411901995154783356551 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard351.root_eq_path] using Shard351.replay
  have hraw020 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (5321766381998068515969 / 256000000000000000000000000 : Rat) + (304411901995154783356551 / 16384000000000000000000000000 : Rat) = (645004950443031168378567 / 16384000000000000000000000000 : Rat))
  have hreplay021 :
      Shard352.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (38510288389856037352599 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard352.root_eq_path] using Shard352.replay
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (645004950443031168378567 / 16384000000000000000000000000 : Rat) + (38510288389856037352599 / 1024000000000000000000000000 : Rat) = (1261169564680727766020151 / 16384000000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (5953365957806366897367 / 81920000000000000000000000 : Rat) + (1261169564680727766020151 / 16384000000000000000000000000 : Rat) = (2451842756242001145493551 / 16384000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (3012808162606379945212527 / 16384000000000000000000000000 : Rat) + (2451842756242001145493551 / 16384000000000000000000000000 : Rat) = (2732325459424190545353039 / 8192000000000000000000000000 : Rat))
  simpa only [tree] using hreplay024

end Branch021
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
