import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard656
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard657
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard658
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard659
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard660
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard661
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard662
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard663
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard664
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard665
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard666
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard667
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard668
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard669
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard670

/-!
# exact P2 forest branch Branch040
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch040

/- Root 2, exact path ((2, 'right'), (1, 'right'), (2, 'right'), (1, 'left')), 348 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard656.tree
          Shard657.tree
        )
        (.split (4 : Fin 6)
          Shard658.tree
          Shard659.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard660.tree
          Shard661.tree
        )
        (.split (0 : Fin 6)
          Shard662.tree
          Shard663.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard664.tree
          Shard665.tree
        )
        (.split (1 : Fin 6)
          Shard666.tree
          Shard667.tree
        )
      )
      (.split (0 : Fin 6)
        Shard668.tree
        (.split (1 : Fin 6)
          Shard669.tree
          Shard670.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard656.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard656.root_eq_path] using Shard656.valid
  have hvalid001 :
      Shard657.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard657.root_eq_path] using Shard657.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard658.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard658.root_eq_path] using Shard658.valid
  have hvalid004 :
      Shard659.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard659.root_eq_path] using Shard659.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard660.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard660.root_eq_path] using Shard660.valid
  have hvalid008 :
      Shard661.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard661.root_eq_path] using Shard661.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard662.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard662.root_eq_path] using Shard662.valid
  have hvalid011 :
      Shard663.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard663.root_eq_path] using Shard663.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard664.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard664.root_eq_path] using Shard664.valid
  have hvalid016 :
      Shard665.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard665.root_eq_path] using Shard665.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard666.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard666.root_eq_path] using Shard666.valid
  have hvalid019 :
      Shard667.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard667.root_eq_path] using Shard667.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard668.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard668.root_eq_path] using Shard668.valid
  have hvalid023 :
      Shard669.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard669.root_eq_path] using Shard669.valid
  have hvalid024 :
      Shard670.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard670.root_eq_path] using Shard670.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid021 hvalid026
  have hvalid028 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
      (2250818912538724123576521 / 1024000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard656.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (768276284223557764243359 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard656.root_eq_path] using Shard656.replay
  have hreplay001 :
      Shard657.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (756706694957680060836531 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard657.root_eq_path] using Shard657.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (768276284223557764243359 / 4096000000000000000000000000 : Rat) + (756706694957680060836531 / 4096000000000000000000000000 : Rat) = (152498297918123782507989 / 409600000000000000000000000 : Rat))
  have hreplay003 :
      Shard658.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (303858723538205842428027 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard658.root_eq_path] using Shard658.replay
  have hreplay004 :
      Shard659.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (714425364237430754869761 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard659.root_eq_path] using Shard659.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (303858723538205842428027 / 2048000000000000000000000000 : Rat) + (714425364237430754869761 / 4096000000000000000000000000 : Rat) = (264428562262768487945163 / 819200000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (152498297918123782507989 / 409600000000000000000000000 : Rat) + (264428562262768487945163 / 819200000000000000000000000 : Rat) = (569425158099016052961141 / 819200000000000000000000000 : Rat))
  have hreplay007 :
      Shard660.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (105170066132761850701617 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard660.root_eq_path] using Shard660.replay
  have hreplay008 :
      Shard661.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (630138134174899130187867 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard661.root_eq_path] using Shard661.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (105170066132761850701617 / 819200000000000000000000000 : Rat) + (630138134174899130187867 / 4096000000000000000000000000 : Rat) = (72249279052419273980997 / 256000000000000000000000000 : Rat))
  have hreplay010 :
      Shard662.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (719637465351683143943649 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard662.root_eq_path] using Shard662.replay
  have hreplay011 :
      Shard663.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (158452632064283695632801 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard663.root_eq_path] using Shard663.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (719637465351683143943649 / 4096000000000000000000000000 : Rat) + (158452632064283695632801 / 819200000000000000000000000 : Rat) = (755950312836550811053827 / 2048000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (72249279052419273980997 / 256000000000000000000000000 : Rat) + (755950312836550811053827 / 2048000000000000000000000000 : Rat) = (1333944545255905002901803 / 2048000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (569425158099016052961141 / 819200000000000000000000000 : Rat) + (1333944545255905002901803 / 2048000000000000000000000000 : Rat) = (5515014881006890270609311 / 4096000000000000000000000000 : Rat))
  have hreplay015 :
      Shard664.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (327232435056599482001883 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard664.root_eq_path] using Shard664.replay
  have hreplay016 :
      Shard665.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (106389050486954373247689 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard665.root_eq_path] using Shard665.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (327232435056599482001883 / 4096000000000000000000000000 : Rat) + (106389050486954373247689 / 1024000000000000000000000000 : Rat) = (752788637004416974992639 / 4096000000000000000000000000 : Rat))
  have hreplay018 :
      Shard666.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (251320540568058059759739 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard666.root_eq_path] using Shard666.replay
  have hreplay019 :
      Shard667.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (277644092582385394770159 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard667.root_eq_path] using Shard667.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (251320540568058059759739 / 2048000000000000000000000000 : Rat) + (277644092582385394770159 / 2048000000000000000000000000 : Rat) = (264482316575221727264949 / 1024000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (752788637004416974992639 / 4096000000000000000000000000 : Rat) + (264482316575221727264949 / 1024000000000000000000000000 : Rat) = (362143580661060776810487 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard668.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (160768596588503346345879 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard668.root_eq_path] using Shard668.replay
  have hreplay023 :
      Shard669.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (492396840013021631956719 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard669.root_eq_path] using Shard669.replay
  have hreplay024 :
      Shard670.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (542071639475667322304103 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard670.root_eq_path] using Shard670.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (492396840013021631956719 / 4096000000000000000000000000 : Rat) + (542071639475667322304103 / 4096000000000000000000000000 : Rat) = (517234239744344477130411 / 2048000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (160768596588503346345879 / 1024000000000000000000000000 : Rat) + (517234239744344477130411 / 2048000000000000000000000000 : Rat) = (838771432921351169822169 / 2048000000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay021 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (362143580661060776810487 / 819200000000000000000000000 : Rat) + (838771432921351169822169 / 2048000000000000000000000000 : Rat) = (3488260769148006223696773 / 4096000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (5515014881006890270609311 / 4096000000000000000000000000 : Rat) + (3488260769148006223696773 / 4096000000000000000000000000 : Rat) = (2250818912538724123576521 / 1024000000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch040
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
