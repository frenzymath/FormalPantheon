import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard079
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard080
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard081
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard082
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard083
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard084
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard085
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard086
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard087
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard088
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard089
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard090
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard091
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard092
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard093
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard094
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard095

/-!
# exact P2 forest branch Branch004
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch004

/- Root 0, exact path ((0, 'right'), (2, 'right'), (1, 'left')), 453 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard079.tree
          Shard080.tree
        )
        (.split (3 : Fin 6)
          Shard081.tree
          Shard082.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          Shard083.tree
          Shard084.tree
        )
        (.split (1 : Fin 6)
          Shard085.tree
          Shard086.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard087.tree
          Shard088.tree
        )
        (.split (0 : Fin 6)
          Shard089.tree
          Shard090.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard091.tree
          Shard092.tree
        )
        (.split (4 : Fin 6)
          Shard093.tree
          (.split (1 : Fin 6)
            Shard094.tree
            Shard095.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard079.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard079.root_eq_path] using Shard079.valid
  have hvalid001 :
      Shard080.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard080.root_eq_path] using Shard080.valid
  have hvalid002 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard081.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard081.root_eq_path] using Shard081.valid
  have hvalid004 :
      Shard082.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard082.root_eq_path] using Shard082.valid
  have hvalid005 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard083.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard083.root_eq_path] using Shard083.valid
  have hvalid008 :
      Shard084.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard084.root_eq_path] using Shard084.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard085.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard085.root_eq_path] using Shard085.valid
  have hvalid011 :
      Shard086.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard086.root_eq_path] using Shard086.valid
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard087.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard087.root_eq_path] using Shard087.valid
  have hvalid016 :
      Shard088.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard088.root_eq_path] using Shard088.valid
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard089.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard089.root_eq_path] using Shard089.valid
  have hvalid019 :
      Shard090.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard090.root_eq_path] using Shard090.valid
  have hvalid020 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard091.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard091.root_eq_path] using Shard091.valid
  have hvalid023 :
      Shard092.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard092.root_eq_path] using Shard092.valid
  have hvalid024 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard093.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard093.root_eq_path] using Shard093.valid
  have hvalid026 :
      Shard094.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard094.root_eq_path] using Shard094.valid
  have hvalid027 :
      Shard095.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard095.root_eq_path] using Shard095.valid
  have hvalid028 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid026 hvalid027
  have hvalid029 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid028
  have hvalid030 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid024 hvalid029
  have hvalid031 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid021 hvalid030
  have hvalid032 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid031
  simpa only [tree] using hvalid032

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
      (25151610892057190532783 / 409600000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard079.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (863157868489503682623 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard079.root_eq_path] using Shard079.replay
  have hreplay001 :
      Shard080.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (394534879156891475937 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard080.root_eq_path] using Shard080.replay
  have hraw002 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (863157868489503682623 / 819200000000000000000000000 : Rat) + (394534879156891475937 / 204800000000000000000000000 : Rat) = (2441297385117069586371 / 819200000000000000000000000 : Rat))
  have hreplay003 :
      Shard081.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (642949533699902308341 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard081.root_eq_path] using Shard081.replay
  have hreplay004 :
      Shard082.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (367041909476696431131 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard082.root_eq_path] using Shard082.replay
  have hraw005 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (642949533699902308341 / 819200000000000000000000000 : Rat) + (367041909476696431131 / 204800000000000000000000000 : Rat) = (422223434321337606573 / 163840000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (2441297385117069586371 / 819200000000000000000000000 : Rat) + (422223434321337606573 / 163840000000000000000000000 : Rat) = (1138103639180939404809 / 204800000000000000000000000 : Rat))
  have hreplay007 :
      Shard083.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (3062463013341911294181 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard083.root_eq_path] using Shard083.replay
  have hreplay008 :
      Shard084.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (937602381316092387687 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard084.root_eq_path] using Shard084.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (3062463013341911294181 / 1638400000000000000000000000 : Rat) + (937602381316092387687 / 327680000000000000000000000 : Rat) = (968809364990296654077 / 204800000000000000000000000 : Rat))
  have hreplay010 :
      Shard085.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (869986253361519669177 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard085.root_eq_path] using Shard085.replay
  have hreplay011 :
      Shard086.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (201650165258576210451 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard086.root_eq_path] using Shard086.replay
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (869986253361519669177 / 819200000000000000000000000 : Rat) + (201650165258576210451 / 163840000000000000000000000 : Rat) = (234779634956800090179 / 102400000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (968809364990296654077 / 204800000000000000000000000 : Rat) + (234779634956800090179 / 102400000000000000000000000 : Rat) = (287673726980779366887 / 40960000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (1138103639180939404809 / 204800000000000000000000000 : Rat) + (287673726980779366887 / 40960000000000000000000000 : Rat) = (644118068521209059811 / 51200000000000000000000000 : Rat))
  have hreplay015 :
      Shard087.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (7417830777024918919779 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard087.root_eq_path] using Shard087.replay
  have hreplay016 :
      Shard088.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (4333729800608505374913 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard088.root_eq_path] using Shard088.replay
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (7417830777024918919779 / 1638400000000000000000000000 : Rat) + (4333729800608505374913 / 819200000000000000000000000 : Rat) = (3217058075648385933921 / 327680000000000000000000000 : Rat))
  have hreplay018 :
      Shard089.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (8601966976831140547899 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard089.root_eq_path] using Shard089.replay
  have hreplay019 :
      Shard090.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2254253729796076079511 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard090.root_eq_path] using Shard090.replay
  have hraw020 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (8601966976831140547899 / 1638400000000000000000000000 : Rat) + (2254253729796076079511 / 819200000000000000000000000 : Rat) = (13110474436423292706921 / 1638400000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (3217058075648385933921 / 327680000000000000000000000 : Rat) + (13110474436423292706921 / 1638400000000000000000000000 : Rat) = (14597882407332611188263 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard091.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (407324316351537482931 / 51200000000000000000000000 : Rat) := by
    simpa only [Shard091.root_eq_path] using Shard091.replay
  have hreplay023 :
      Shard092.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (363986724575867231817 / 65536000000000000000000000 : Rat) := by
    simpa only [Shard092.root_eq_path] using Shard092.replay
  have hraw024 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (407324316351537482931 / 51200000000000000000000000 : Rat) + (363986724575867231817 / 65536000000000000000000000 : Rat) = (22134046237645880249217 / 1638400000000000000000000000 : Rat))
  have hreplay025 :
      Shard093.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (324792169987849971957 / 51200000000000000000000000 : Rat) := by
    simpa only [Shard093.root_eq_path] using Shard093.replay
  have hreplay026 :
      Shard094.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (5294085999792265116441 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard094.root_eq_path] using Shard094.replay
  have hreplay027 :
      Shard095.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7683332884043240255931 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard095.root_eq_path] using Shard095.replay
  have hraw028 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay026 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (5294085999792265116441 / 819200000000000000000000000 : Rat) + (7683332884043240255931 / 1638400000000000000000000000 : Rat) = (18271504883627770488813 / 1638400000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (324792169987849971957 / 51200000000000000000000000 : Rat) + (18271504883627770488813 / 1638400000000000000000000000 : Rat) = (28664854323238969591437 / 1638400000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay024 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (22134046237645880249217 / 1638400000000000000000000000 : Rat) + (28664854323238969591437 / 1638400000000000000000000000 : Rat) = (25399450280442424920327 / 819200000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay021 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (14597882407332611188263 / 819200000000000000000000000 : Rat) + (25399450280442424920327 / 819200000000000000000000000 : Rat) = (3999733268777503610859 / 81920000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (644118068521209059811 / 51200000000000000000000000 : Rat) + (3999733268777503610859 / 81920000000000000000000000 : Rat) = (25151610892057190532783 / 409600000000000000000000000 : Rat))
  simpa only [tree] using hreplay032

end Branch004
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
