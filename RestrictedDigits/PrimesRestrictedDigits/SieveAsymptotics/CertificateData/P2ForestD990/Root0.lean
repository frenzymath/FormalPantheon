import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard002
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard003
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard005
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard007
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard008
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard009
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard011
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard012
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard013
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard014
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard015
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard016
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch002
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch003
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch005

/-!
# exact P2 forest root Root0
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Root0

/- Root 0, exact path (), 2546 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (2 : Fin 6)
      (.split (0 : Fin 6)
        (.split (2 : Fin 6)
          (.split (3 : Fin 6)
            (.split (2 : Fin 6)
              Shard000.tree
              Shard001.tree
            )
            (.split (4 : Fin 6)
              Shard002.tree
              Shard003.tree
            )
          )
          (.split (0 : Fin 6)
            (.split (3 : Fin 6)
              Shard004.tree
              Shard005.tree
            )
            (.split (1 : Fin 6)
              Shard006.tree
              Shard007.tree
            )
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            (.split (2 : Fin 6)
              Shard008.tree
              Shard009.tree
            )
            (.split (3 : Fin 6)
              Shard010.tree
              Shard011.tree
            )
          )
          (.split (1 : Fin 6)
            (.split (3 : Fin 6)
              Shard012.tree
              Shard013.tree
            )
            (.split (2 : Fin 6)
              Shard014.tree
              (.split (0 : Fin 6)
                Shard015.tree
                Shard016.tree
              )
            )
          )
        )
      )
      (.split (0 : Fin 6)
        Branch000.tree
        Branch001.tree
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        Branch002.tree
        Branch003.tree
      )
      (.split (1 : Fin 6)
        Branch004.tree
        Branch005.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (sectionSixP2RootD974 (0 : Fin 3)) = true := by
  have hvalid000 :
      Shard000.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard000.root_eq_path] using Shard000.valid
  have hvalid001 :
      Shard001.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard001.root_eq_path] using Shard001.valid
  have hvalid002 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard002.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard002.root_eq_path] using Shard002.valid
  have hvalid004 :
      Shard003.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard003.root_eq_path] using Shard003.valid
  have hvalid005 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard004.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard004.root_eq_path] using Shard004.valid
  have hvalid008 :
      Shard005.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard005.root_eq_path] using Shard005.valid
  have hvalid009 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard006.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard006.root_eq_path] using Shard006.valid
  have hvalid011 :
      Shard007.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard007.root_eq_path] using Shard007.valid
  have hvalid012 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard008.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard008.root_eq_path] using Shard008.valid
  have hvalid016 :
      Shard009.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard009.root_eq_path] using Shard009.valid
  have hvalid017 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard010.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard010.root_eq_path] using Shard010.valid
  have hvalid019 :
      Shard011.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard011.root_eq_path] using Shard011.valid
  have hvalid020 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard012.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard012.root_eq_path] using Shard012.valid
  have hvalid023 :
      Shard013.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard013.root_eq_path] using Shard013.valid
  have hvalid024 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard014.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard014.root_eq_path] using Shard014.valid
  have hvalid026 :
      Shard015.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard015.root_eq_path] using Shard015.valid
  have hvalid027 :
      Shard016.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard016.root_eq_path] using Shard016.valid
  have hvalid028 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid026 hvalid027
  have hvalid029 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid025 hvalid028
  have hvalid030 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid024 hvalid029
  have hvalid031 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid021 hvalid030
  have hvalid032 :=
    valid_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid014 hvalid031
  have hvalid033 :
      Branch000.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    exact Branch000.valid
  have hvalid034 :
      Branch001.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    exact Branch001.valid
  have hvalid035 :=
    valid_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid033 hvalid034
  have hvalid036 :=
    valid_split (T := (sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid032 hvalid035
  have hvalid037 :
      Branch002.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch002.valid
  have hvalid038 :
      Branch003.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch003.valid
  have hvalid039 :=
    valid_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid037 hvalid038
  have hvalid040 :
      Branch004.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    exact Branch004.valid
  have hvalid041 :
      Branch005.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    exact Branch005.valid
  have hvalid042 :=
    valid_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid040 hvalid041
  have hvalid043 :=
    valid_split (T := (sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid039 hvalid042
  have hvalid044 :=
    valid_split (T := sectionSixP2RootD974 (0 : Fin 3)) (e := (0 : Fin 6)) hvalid036 hvalid043
  simpa only [tree] using hvalid044

theorem replay :
    tree.replayWeightRat (sectionSixP2RootD974 (0 : Fin 3)) (fun _ p => p.upper) =
      (547338059614207315563219 / 819200000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard000.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1953821382779630751057 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard000.root_eq_path] using Shard000.replay
  have hreplay001 :
      Shard001.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1458426237835466992257 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard001.root_eq_path] using Shard001.replay
  have hraw002 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (1953821382779630751057 / 409600000000000000000000000 : Rat) + (1458426237835466992257 / 204800000000000000000000000 : Rat) = (4870673858450564735571 / 409600000000000000000000000 : Rat))
  have hreplay003 :
      Shard002.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1942234362687555546291 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard002.root_eq_path] using Shard002.replay
  have hreplay004 :
      Shard003.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (347262064858249681833 / 20480000000000000000000000 : Rat) := by
    simpa only [Shard003.root_eq_path] using Shard003.replay
  have hraw005 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (1942234362687555546291 / 204800000000000000000000000 : Rat) + (347262064858249681833 / 20480000000000000000000000 : Rat) = (5414855011270052364621 / 204800000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (4870673858450564735571 / 409600000000000000000000000 : Rat) + (5414855011270052364621 / 204800000000000000000000000 : Rat) = (15700383880990669464813 / 409600000000000000000000000 : Rat))
  have hreplay007 :
      Shard004.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (9867001778759814837687 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard004.root_eq_path] using Shard004.replay
  have hreplay008 :
      Shard005.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (997895947788529199883 / 51200000000000000000000000 : Rat) := by
    simpa only [Shard005.root_eq_path] using Shard005.replay
  have hraw009 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (9867001778759814837687 / 819200000000000000000000000 : Rat) + (997895947788529199883 / 51200000000000000000000000 : Rat) = (5166667388675256407163 / 163840000000000000000000000 : Rat))
  have hreplay010 :
      Shard006.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (440044412199789112353 / 40960000000000000000000000 : Rat) := by
    simpa only [Shard006.root_eq_path] using Shard006.replay
  have hreplay011 :
      Shard007.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (12863039105669809690161 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard007.root_eq_path] using Shard007.replay
  have hraw012 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (440044412199789112353 / 40960000000000000000000000 : Rat) + (12863039105669809690161 / 819200000000000000000000000 : Rat) = (21663927349665591937221 / 819200000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (5166667388675256407163 / 163840000000000000000000000 : Rat) + (21663927349665591937221 / 819200000000000000000000000 : Rat) = (11874316073260468493259 / 204800000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (15700383880990669464813 / 409600000000000000000000000 : Rat) + (11874316073260468493259 / 204800000000000000000000000 : Rat) = (39449016027511606451331 / 409600000000000000000000000 : Rat))
  have hreplay015 :
      Shard008.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1144686188096121787083 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard008.root_eq_path] using Shard008.replay
  have hreplay016 :
      Shard009.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1528899736026774911283 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard009.root_eq_path] using Shard009.replay
  have hraw017 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (1144686188096121787083 / 409600000000000000000000000 : Rat) + (1528899736026774911283 / 409600000000000000000000000 : Rat) = (1336792962061448349183 / 204800000000000000000000000 : Rat))
  have hreplay018 :
      Shard010.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (2279862867180257976573 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard010.root_eq_path] using Shard010.replay
  have hreplay019 :
      Shard011.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (8602772850391318112943 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard011.root_eq_path] using Shard011.replay
  have hraw020 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (2279862867180257976573 / 409600000000000000000000000 : Rat) + (8602772850391318112943 / 819200000000000000000000000 : Rat) = (13162498584751834066089 / 819200000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (1336792962061448349183 / 204800000000000000000000000 : Rat) + (13162498584751834066089 / 819200000000000000000000000 : Rat) = (18509670432997627462821 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard012.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (889463543171961169071 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard012.root_eq_path] using Shard012.replay
  have hreplay023 :
      Shard013.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (1502099145848743955271 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard013.root_eq_path] using Shard013.replay
  have hraw024 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (889463543171961169071 / 204800000000000000000000000 : Rat) + (1502099145848743955271 / 163840000000000000000000000 : Rat) = (11068349901931564452639 / 819200000000000000000000000 : Rat))
  have hreplay025 :
      Shard014.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (6892341679154465565867 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard014.root_eq_path] using Shard014.replay
  have hreplay026 :
      Shard015.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2264968570751129321991 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard015.root_eq_path] using Shard015.replay
  have hreplay027 :
      Shard016.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (3349923894349009829181 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard016.root_eq_path] using Shard016.replay
  have hraw028 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay026 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (2264968570751129321991 / 409600000000000000000000000 : Rat) + (3349923894349009829181 / 819200000000000000000000000 : Rat) = (7879861035851268473163 / 819200000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay025 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (6892341679154465565867 / 819200000000000000000000000 : Rat) + (7879861035851268473163 / 819200000000000000000000000 : Rat) = (1477220271500573403903 / 81920000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay024 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (11068349901931564452639 / 819200000000000000000000000 : Rat) + (1477220271500573403903 / 81920000000000000000000000 : Rat) = (25840552616937298491669 / 819200000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay021 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (18509670432997627462821 / 819200000000000000000000000 : Rat) + (25840552616937298491669 / 819200000000000000000000000 : Rat) = (4435022304993492595449 / 81920000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay014 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (39449016027511606451331 / 409600000000000000000000000 : Rat) + (4435022304993492595449 / 81920000000000000000000000 : Rat) = (1925753986014970919643 / 12800000000000000000000000 : Rat))
  have hreplay033 :
      Branch000.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (104877929457854515800189 / 819200000000000000000000000 : Rat) := by
    exact Branch000.replay
  have hreplay034 :
      Branch001.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (193361599608859632709143 / 1638400000000000000000000000 : Rat) := by
    exact Branch001.replay
  have hraw035 :=
    replay_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay033 hreplay034
  have hreplay035 := hraw035.trans
    (by norm_num : (104877929457854515800189 / 819200000000000000000000000 : Rat) + (193361599608859632709143 / 1638400000000000000000000000 : Rat) = (403117458524568664309521 / 1638400000000000000000000000 : Rat))
  have hraw036 :=
    replay_split (T := (sectionSixP2RootD974 (0 : Fin 3)).leftChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay032 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (1925753986014970919643 / 12800000000000000000000000 : Rat) + (403117458524568664309521 / 1638400000000000000000000000 : Rat) = (25984558749379397680953 / 65536000000000000000000000 : Rat))
  have hreplay037 :
      Branch002.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (15404952536146529953839 / 819200000000000000000000000 : Rat) := by
    exact Branch002.replay
  have hreplay038 :
      Branch003.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (118076077766053126848447 / 1638400000000000000000000000 : Rat) := by
    exact Branch003.replay
  have hraw039 :=
    replay_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay037 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (15404952536146529953839 / 819200000000000000000000000 : Rat) + (118076077766053126848447 / 1638400000000000000000000000 : Rat) = (1191087862706769494049 / 13107200000000000000000000 : Rat))
  have hreplay040 :
      Branch004.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (25151610892057190532783 / 409600000000000000000000000 : Rat) := by
    exact Branch004.replay
  have hreplay041 :
      Branch005.tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (48892431021838685053839 / 409600000000000000000000000 : Rat) := by
    exact Branch005.replay
  have hraw042 :=
    replay_split (T := ((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay040 hreplay041
  have hreplay042 := hraw042.trans
    (by norm_num : (25151610892057190532783 / 409600000000000000000000000 : Rat) + (48892431021838685053839 / 409600000000000000000000000 : Rat) = (37022020956947937793311 / 204800000000000000000000000 : Rat))
  have hraw043 :=
    replay_split (T := (sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay039 hreplay042
  have hreplay043 := hraw043.trans
    (by norm_num : (1191087862706769494049 / 13107200000000000000000000 : Rat) + (37022020956947937793311 / 204800000000000000000000000 : Rat) = (445062150493929689102613 / 1638400000000000000000000000 : Rat))
  have hraw044 :=
    replay_split (T := sectionSixP2RootD974 (0 : Fin 3)) (e := (0 : Fin 6)) hreplay036 hreplay043
  have hreplay044 := hraw044.trans
    (by norm_num : (25984558749379397680953 / 65536000000000000000000000 : Rat) + (445062150493929689102613 / 1638400000000000000000000000 : Rat) = (547338059614207315563219 / 819200000000000000000000000 : Rat))
  simpa only [tree] using hreplay044

end Root0
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
