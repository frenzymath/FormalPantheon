import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard033
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard034
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard035
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard036
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard037
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard038
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard039
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard040
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard041
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard042
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard043
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard044
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard045
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard046
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard047
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard048
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard049
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard050

/-!
# exact P2 forest branch Branch001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch001

/- Root 0, exact path ((0, 'left'), (2, 'right'), (0, 'right')), 363 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard033.tree
          Shard034.tree
        )
        (.split (0 : Fin 6)
          Shard035.tree
          Shard036.tree
        )
      )
      (.split (3 : Fin 6)
        Shard037.tree
        (.split (3 : Fin 6)
          Shard038.tree
          Shard039.tree
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (2 : Fin 6)
        (.split (0 : Fin 6)
          Shard040.tree
          Shard041.tree
        )
        (.split (0 : Fin 6)
          Shard042.tree
          Shard043.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            Shard044.tree
            Shard045.tree
          )
          (.split (1 : Fin 6)
            Shard046.tree
            Shard047.tree
          )
        )
        (.split (1 : Fin 6)
          Shard048.tree
          (.split (2 : Fin 6)
            Shard049.tree
            Shard050.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard033.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard033.root_eq_path] using Shard033.valid
  have hvalid001 :
      Shard034.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard034.root_eq_path] using Shard034.valid
  have hvalid002 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard035.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard035.root_eq_path] using Shard035.valid
  have hvalid004 :
      Shard036.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard036.root_eq_path] using Shard036.valid
  have hvalid005 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard037.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard037.root_eq_path] using Shard037.valid
  have hvalid008 :
      Shard038.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard038.root_eq_path] using Shard038.valid
  have hvalid009 :
      Shard039.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard039.root_eq_path] using Shard039.valid
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard040.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard040.root_eq_path] using Shard040.valid
  have hvalid014 :
      Shard041.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard041.root_eq_path] using Shard041.valid
  have hvalid015 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard042.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard042.root_eq_path] using Shard042.valid
  have hvalid017 :
      Shard043.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard043.root_eq_path] using Shard043.valid
  have hvalid018 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard044.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard044.root_eq_path] using Shard044.valid
  have hvalid021 :
      Shard045.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard045.root_eq_path] using Shard045.valid
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :
      Shard046.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard046.root_eq_path] using Shard046.valid
  have hvalid024 :
      Shard047.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard047.root_eq_path] using Shard047.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :
      Shard048.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard048.root_eq_path] using Shard048.valid
  have hvalid028 :
      Shard049.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard049.root_eq_path] using Shard049.valid
  have hvalid029 :
      Shard050.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard050.root_eq_path] using Shard050.valid
  have hvalid030 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid027 hvalid030
  have hvalid032 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid026 hvalid031
  have hvalid033 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid019 hvalid032
  have hvalid034 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid012 hvalid033
  simpa only [tree] using hvalid034

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
      (193361599608859632709143 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard033.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (372129035636528723223 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard033.root_eq_path] using Shard033.replay
  have hreplay001 :
      Shard034.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (1041421579650386744337 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard034.root_eq_path] using Shard034.replay
  have hraw002 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (372129035636528723223 / 102400000000000000000000000 : Rat) + (1041421579650386744337 / 409600000000000000000000000 : Rat) = (2529937722196501637229 / 409600000000000000000000000 : Rat))
  have hreplay003 :
      Shard035.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (3590127928497352603977 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard035.root_eq_path] using Shard035.replay
  have hreplay004 :
      Shard036.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (3253718484815149241847 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard036.root_eq_path] using Shard036.replay
  have hraw005 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (3590127928497352603977 / 819200000000000000000000000 : Rat) + (3253718484815149241847 / 819200000000000000000000000 : Rat) = (106935100208007841341 / 12800000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (2529937722196501637229 / 409600000000000000000000000 : Rat) + (106935100208007841341 / 12800000000000000000000000 : Rat) = (5951860928852752560141 / 409600000000000000000000000 : Rat))
  have hreplay007 :
      Shard037.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (9890437240374475846941 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard037.root_eq_path] using Shard037.replay
  have hreplay008 :
      Shard038.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (599522730898327616061 / 81920000000000000000000000 : Rat) := by
    simpa only [Shard038.root_eq_path] using Shard038.replay
  have hreplay009 :
      Shard039.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (6854362829083700741151 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard039.root_eq_path] using Shard039.replay
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (599522730898327616061 / 81920000000000000000000000 : Rat) + (6854362829083700741151 / 819200000000000000000000000 : Rat) = (12849590138066976901761 / 819200000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (9890437240374475846941 / 819200000000000000000000000 : Rat) + (12849590138066976901761 / 819200000000000000000000000 : Rat) = (11370013689220726374351 / 409600000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (5951860928852752560141 / 409600000000000000000000000 : Rat) + (11370013689220726374351 / 409600000000000000000000000 : Rat) = (4330468654518369733623 / 102400000000000000000000000 : Rat))
  have hreplay013 :
      Shard040.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (3277491015954933860841 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard040.root_eq_path] using Shard040.replay
  have hreplay014 :
      Shard041.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (4996274091251610772539 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard041.root_eq_path] using Shard041.replay
  have hraw015 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (3277491015954933860841 / 409600000000000000000000000 : Rat) + (4996274091251610772539 / 819200000000000000000000000 : Rat) = (11551256123161478494221 / 819200000000000000000000000 : Rat))
  have hreplay016 :
      Shard042.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (146040011709982567353 / 16384000000000000000000000 : Rat) := by
    simpa only [Shard042.root_eq_path] using Shard042.replay
  have hreplay017 :
      Shard043.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (6373926933609425570127 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard043.root_eq_path] using Shard043.replay
  have hraw018 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (146040011709982567353 / 16384000000000000000000000 : Rat) + (6373926933609425570127 / 819200000000000000000000000 : Rat) = (13675927519108553937777 / 819200000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (11551256123161478494221 / 819200000000000000000000000 : Rat) + (13675927519108553937777 / 819200000000000000000000000 : Rat) = (12613591821135016215999 / 409600000000000000000000000 : Rat))
  have hreplay020 :
      Shard044.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2055474907849570632183 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard044.root_eq_path] using Shard044.replay
  have hreplay021 :
      Shard045.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (9089776492024740143049 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard045.root_eq_path] using Shard045.replay
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (2055474907849570632183 / 409600000000000000000000000 : Rat) + (9089776492024740143049 / 1638400000000000000000000000 : Rat) = (17311676123423022671781 / 1638400000000000000000000000 : Rat))
  have hreplay023 :
      Shard046.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (482682129169160536407 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard046.root_eq_path] using Shard046.replay
  have hreplay024 :
      Shard047.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (10220075925988298975451 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard047.root_eq_path] using Shard047.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (482682129169160536407 / 102400000000000000000000000 : Rat) + (10220075925988298975451 / 1638400000000000000000000000 : Rat) = (17942989992694867557963 / 1638400000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (17311676123423022671781 / 1638400000000000000000000000 : Rat) + (17942989992694867557963 / 1638400000000000000000000000 : Rat) = (2203416632257368139359 / 102400000000000000000000000 : Rat))
  have hreplay027 :
      Shard048.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7925536555128087280803 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard048.root_eq_path] using Shard048.replay
  have hreplay028 :
      Shard049.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2030925751742434983183 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard049.root_eq_path] using Shard049.replay
  have hreplay029 :
      Shard050.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (6179682933469706199957 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard050.root_eq_path] using Shard050.replay
  have hraw030 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (2030925751742434983183 / 327680000000000000000000000 : Rat) + (6179682933469706199957 / 819200000000000000000000000 : Rat) = (22513994625651587315829 / 1638400000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay027 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (7925536555128087280803 / 819200000000000000000000000 : Rat) + (22513994625651587315829 / 1638400000000000000000000000 : Rat) = (7673013547181552375487 / 327680000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay026 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (2203416632257368139359 / 102400000000000000000000000 : Rat) + (7673013547181552375487 / 327680000000000000000000000 : Rat) = (73619733852025652107179 / 1638400000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay019 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (12613591821135016215999 / 409600000000000000000000000 : Rat) + (73619733852025652107179 / 1638400000000000000000000000 : Rat) = (4962964045462628678847 / 65536000000000000000000000 : Rat))
  have hraw034 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay012 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (4330468654518369733623 / 102400000000000000000000000 : Rat) + (4962964045462628678847 / 65536000000000000000000000 : Rat) = (193361599608859632709143 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay034

end Branch001
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
