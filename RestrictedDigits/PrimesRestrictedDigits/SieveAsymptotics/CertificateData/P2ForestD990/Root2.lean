import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch020
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch021
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch022
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch023
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch024
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch025
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch026
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch027
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch028
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch029
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch030
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch031
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch032
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch033
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch034
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch035
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch036
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch037
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch038
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch039
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch040
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch041

/-!
# exact P2 forest root Root2
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Root2

/- Root 2, exact path (), 7728 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            Branch020.tree
            Branch021.tree
          )
          (.split (1 : Fin 6)
            Branch022.tree
            Branch023.tree
          )
        )
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            Branch024.tree
            Branch025.tree
          )
          (.split (2 : Fin 6)
            Branch026.tree
            Branch027.tree
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          Branch028.tree
          Branch029.tree
        )
        (.split (4 : Fin 6)
          Branch030.tree
          Branch031.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            Branch032.tree
            Branch033.tree
          )
          (.split (1 : Fin 6)
            Branch034.tree
            Branch035.tree
          )
        )
        (.split (4 : Fin 6)
          Branch036.tree
          Branch037.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Branch038.tree
          Branch039.tree
        )
        (.split (1 : Fin 6)
          Branch040.tree
          Branch041.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (sectionSixP2RootD974 (2 : Fin 3)) = true := by
  have hvalid000 :
      Branch020.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch020.valid
  have hvalid001 :
      Branch021.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch021.valid
  have hvalid002 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Branch022.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    exact Branch022.valid
  have hvalid004 :
      Branch023.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    exact Branch023.valid
  have hvalid005 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Branch024.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    exact Branch024.valid
  have hvalid008 :
      Branch025.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    exact Branch025.valid
  have hvalid009 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Branch026.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    exact Branch026.valid
  have hvalid011 :
      Branch027.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    exact Branch027.valid
  have hvalid012 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Branch028.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    exact Branch028.valid
  have hvalid016 :
      Branch029.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    exact Branch029.valid
  have hvalid017 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Branch030.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch030.valid
  have hvalid019 :
      Branch031.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch031.valid
  have hvalid020 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :=
    valid_split (T := (sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid014 hvalid021
  have hvalid023 :
      Branch032.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    exact Branch032.valid
  have hvalid024 :
      Branch033.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    exact Branch033.valid
  have hvalid025 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :
      Branch034.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    exact Branch034.valid
  have hvalid027 :
      Branch035.tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    exact Branch035.valid
  have hvalid028 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid026 hvalid027
  have hvalid029 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid025 hvalid028
  have hvalid030 :
      Branch036.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch036.valid
  have hvalid031 :
      Branch037.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch037.valid
  have hvalid032 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid030 hvalid031
  have hvalid033 :=
    valid_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid029 hvalid032
  have hvalid034 :
      Branch038.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch038.valid
  have hvalid035 :
      Branch039.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch039.valid
  have hvalid036 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid034 hvalid035
  have hvalid037 :
      Branch040.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    exact Branch040.valid
  have hvalid038 :
      Branch041.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    exact Branch041.valid
  have hvalid039 :=
    valid_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid037 hvalid038
  have hvalid040 :=
    valid_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid036 hvalid039
  have hvalid041 :=
    valid_split (T := (sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid033 hvalid040
  have hvalid042 :=
    valid_split (T := sectionSixP2RootD974 (2 : Fin 3)) (e := (2 : Fin 6)) hvalid022 hvalid041
  simpa only [tree] using hvalid042

theorem replay :
    tree.replayWeightRat (sectionSixP2RootD974 (2 : Fin 3)) (fun _ p => p.upper) =
      (81300800710497560233812003 / 3276800000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch020.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (333676292060199655943433 / 1024000000000000000000000000 : Rat) := by
    exact Branch020.replay
  have hreplay001 :
      Branch021.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2732325459424190545353039 / 8192000000000000000000000000 : Rat) := by
    exact Branch021.replay
  have hraw002 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (333676292060199655943433 / 1024000000000000000000000000 : Rat) + (2732325459424190545353039 / 8192000000000000000000000000 : Rat) = (5401735795905787792900503 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Branch022.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (6531118995960691932611943 / 16384000000000000000000000000 : Rat) := by
    exact Branch022.replay
  have hreplay004 :
      Branch023.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (580794912688643811663273 / 1638400000000000000000000000 : Rat) := by
    exact Branch023.replay
  have hraw005 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (6531118995960691932611943 / 16384000000000000000000000000 : Rat) + (580794912688643811663273 / 1638400000000000000000000000 : Rat) = (12339068122847130049244673 / 16384000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (5401735795905787792900503 / 8192000000000000000000000000 : Rat) + (12339068122847130049244673 / 16384000000000000000000000000 : Rat) = (23142539714658705635045679 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Branch024.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1824446753925759801957717 / 3276800000000000000000000000 : Rat) := by
    exact Branch024.replay
  have hreplay008 :
      Branch025.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (865401282225865321193187 / 1638400000000000000000000000 : Rat) := by
    exact Branch025.replay
  have hraw009 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (1824446753925759801957717 / 3276800000000000000000000000 : Rat) + (865401282225865321193187 / 1638400000000000000000000000 : Rat) = (3555249318377490444344091 / 3276800000000000000000000000 : Rat))
  have hreplay010 :
      Branch026.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (3300998390904745741653873 / 4096000000000000000000000000 : Rat) := by
    exact Branch026.replay
  have hreplay011 :
      Branch027.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (704960426602484236893177 / 1024000000000000000000000000 : Rat) := by
    exact Branch027.replay
  have hraw012 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (3300998390904745741653873 / 4096000000000000000000000000 : Rat) + (704960426602484236893177 / 1024000000000000000000000000 : Rat) = (6120840097314682689226581 / 4096000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (3555249318377490444344091 / 3276800000000000000000000000 : Rat) + (6120840097314682689226581 / 4096000000000000000000000000 : Rat) = (42259606981146182978626779 / 16384000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (23142539714658705635045679 / 16384000000000000000000000000 : Rat) + (42259606981146182978626779 / 16384000000000000000000000000 : Rat) = (32701073347902444306836229 / 8192000000000000000000000000 : Rat))
  have hreplay015 :
      Branch028.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (879763381511492521311777 / 512000000000000000000000000 : Rat) := by
    exact Branch028.replay
  have hreplay016 :
      Branch029.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (5199870362530362664125051 / 3276800000000000000000000000 : Rat) := by
    exact Branch029.replay
  have hraw017 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (879763381511492521311777 / 512000000000000000000000000 : Rat) + (5199870362530362664125051 / 3276800000000000000000000000 : Rat) = (54151780021019574002602119 / 16384000000000000000000000000 : Rat))
  have hreplay018 :
      Branch030.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (4338719621264294493180939 / 4096000000000000000000000000 : Rat) := by
    exact Branch030.replay
  have hreplay019 :
      Branch031.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (3909825496749259046611089 / 3276800000000000000000000000 : Rat) := by
    exact Branch031.replay
  have hraw020 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (4338719621264294493180939 / 4096000000000000000000000000 : Rat) + (3909825496749259046611089 / 3276800000000000000000000000 : Rat) = (36904005968803473205779201 / 16384000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (54151780021019574002602119 / 16384000000000000000000000000 : Rat) + (36904005968803473205779201 / 16384000000000000000000000000 : Rat) = (2276394649745576180209533 / 409600000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay014 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (32701073347902444306836229 / 8192000000000000000000000000 : Rat) + (2276394649745576180209533 / 409600000000000000000000000 : Rat) = (78228966342813967911026889 / 8192000000000000000000000000 : Rat))
  have hreplay023 :
      Branch032.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (4094054545944017351419209 / 3276800000000000000000000000 : Rat) := by
    exact Branch032.replay
  have hreplay024 :
      Branch033.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (9867054873231400335271407 / 8192000000000000000000000000 : Rat) := by
    exact Branch033.replay
  have hraw025 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (4094054545944017351419209 / 3276800000000000000000000000 : Rat) + (9867054873231400335271407 / 8192000000000000000000000000 : Rat) = (40204382476182887427638859 / 16384000000000000000000000000 : Rat))
  have hreplay026 :
      Branch034.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (20630302451500713758269623 / 16384000000000000000000000000 : Rat) := by
    exact Branch034.replay
  have hreplay027 :
      Branch035.tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (207108160483210628569101 / 163840000000000000000000000 : Rat) := by
    exact Branch035.replay
  have hraw028 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay026 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (20630302451500713758269623 / 16384000000000000000000000000 : Rat) + (207108160483210628569101 / 163840000000000000000000000 : Rat) = (41341118499821776615179723 / 16384000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay025 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (40204382476182887427638859 / 16384000000000000000000000000 : Rat) + (41341118499821776615179723 / 16384000000000000000000000000 : Rat) = (40772750488002332021409291 / 8192000000000000000000000000 : Rat))
  have hreplay030 :
      Branch036.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (29853130000296677376944457 / 16384000000000000000000000000 : Rat) := by
    exact Branch036.replay
  have hreplay031 :
      Branch037.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (16916013883555292440369431 / 8192000000000000000000000000 : Rat) := by
    exact Branch037.replay
  have hraw032 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay030 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (29853130000296677376944457 / 16384000000000000000000000000 : Rat) + (16916013883555292440369431 / 8192000000000000000000000000 : Rat) = (63685157767407262257683319 / 16384000000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay029 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (40772750488002332021409291 / 8192000000000000000000000000 : Rat) + (63685157767407262257683319 / 16384000000000000000000000000 : Rat) = (145230658743411926300501901 / 16384000000000000000000000000 : Rat))
  have hreplay034 :
      Branch038.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (5836753972903449215310867 / 4096000000000000000000000000 : Rat) := by
    exact Branch038.replay
  have hreplay035 :
      Branch039.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (6105885045201887837477931 / 4096000000000000000000000000 : Rat) := by
    exact Branch039.replay
  have hraw036 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay034 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (5836753972903449215310867 / 4096000000000000000000000000 : Rat) + (6105885045201887837477931 / 4096000000000000000000000000 : Rat) = (5971319509052668526394399 / 2048000000000000000000000000 : Rat))
  have hreplay037 :
      Branch040.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (2250818912538724123576521 / 1024000000000000000000000000 : Rat) := by
    exact Branch040.replay
  have hreplay038 :
      Branch041.tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (2628969181300875607265601 / 2048000000000000000000000000 : Rat) := by
    exact Branch041.replay
  have hraw039 :=
    replay_split (T := (((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay037 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (2250818912538724123576521 / 1024000000000000000000000000 : Rat) + (2628969181300875607265601 / 2048000000000000000000000000 : Rat) = (7130607006378323854418643 / 2048000000000000000000000000 : Rat))
  have hraw040 :=
    replay_split (T := ((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay036 hreplay039
  have hreplay040 := hraw040.trans
    (by norm_num : (5971319509052668526394399 / 2048000000000000000000000000 : Rat) + (7130607006378323854418643 / 2048000000000000000000000000 : Rat) = (6550963257715496190406521 / 1024000000000000000000000000 : Rat))
  have hraw041 :=
    replay_split (T := (sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay033 hreplay040
  have hreplay041 := hraw041.trans
    (by norm_num : (145230658743411926300501901 / 16384000000000000000000000000 : Rat) + (6550963257715496190406521 / 1024000000000000000000000000 : Rat) = (250046070866859865347006237 / 16384000000000000000000000000 : Rat))
  have hraw042 :=
    replay_split (T := sectionSixP2RootD974 (2 : Fin 3)) (e := (2 : Fin 6)) hreplay022 hreplay041
  have hreplay042 := hraw042.trans
    (by norm_num : (78228966342813967911026889 / 8192000000000000000000000000 : Rat) + (250046070866859865347006237 / 16384000000000000000000000000 : Rat) = (81300800710497560233812003 / 3276800000000000000000000000 : Rat))
  simpa only [tree] using hreplay042

end Root2
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
