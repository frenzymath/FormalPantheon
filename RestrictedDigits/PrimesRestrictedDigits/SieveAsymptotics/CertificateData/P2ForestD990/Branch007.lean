import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard129
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard130
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard131
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard132
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard133
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard134
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard135
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard136
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard137
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard138
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard139
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard140
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard141
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard142
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard143
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard144
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard145
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard146

/-!
# exact P2 forest branch Branch007
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch007

/- Root 1, exact path ((1, 'left'), (3, 'left'), (1, 'left'), (3, 'right')), 354 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard129.tree
          Shard130.tree
        )
        (.split (5 : Fin 6)
          Shard131.tree
          (.split (0 : Fin 6)
            Shard132.tree
            Shard133.tree
          )
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard134.tree
          Shard135.tree
        )
        (.split (0 : Fin 6)
          Shard136.tree
          Shard137.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (4 : Fin 6)
        (.split (3 : Fin 6)
          Shard138.tree
          Shard139.tree
        )
        (.split (3 : Fin 6)
          Shard140.tree
          Shard141.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard142.tree
          Shard143.tree
        )
        (.split (0 : Fin 6)
          (.split (4 : Fin 6)
            Shard144.tree
            Shard145.tree
          )
          Shard146.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard129.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard129.root_eq_path] using Shard129.valid
  have hvalid001 :
      Shard130.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard130.root_eq_path] using Shard130.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard131.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard131.root_eq_path] using Shard131.valid
  have hvalid004 :
      Shard132.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard132.root_eq_path] using Shard132.valid
  have hvalid005 :
      Shard133.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard133.root_eq_path] using Shard133.valid
  have hvalid006 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hvalid004 hvalid005
  have hvalid007 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid003 hvalid006
  have hvalid008 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid007
  have hvalid009 :
      Shard134.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard134.root_eq_path] using Shard134.valid
  have hvalid010 :
      Shard135.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard135.root_eq_path] using Shard135.valid
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid009 hvalid010
  have hvalid012 :
      Shard136.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard136.root_eq_path] using Shard136.valid
  have hvalid013 :
      Shard137.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard137.root_eq_path] using Shard137.valid
  have hvalid014 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid012 hvalid013
  have hvalid015 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid011 hvalid014
  have hvalid016 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid008 hvalid015
  have hvalid017 :
      Shard138.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard138.root_eq_path] using Shard138.valid
  have hvalid018 :
      Shard139.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard139.root_eq_path] using Shard139.valid
  have hvalid019 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid017 hvalid018
  have hvalid020 :
      Shard140.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard140.root_eq_path] using Shard140.valid
  have hvalid021 :
      Shard141.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard141.root_eq_path] using Shard141.valid
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid019 hvalid022
  have hvalid024 :
      Shard142.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard142.root_eq_path] using Shard142.valid
  have hvalid025 :
      Shard143.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard143.root_eq_path] using Shard143.valid
  have hvalid026 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid024 hvalid025
  have hvalid027 :
      Shard144.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard144.root_eq_path] using Shard144.valid
  have hvalid028 :
      Shard145.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard145.root_eq_path] using Shard145.valid
  have hvalid029 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid027 hvalid028
  have hvalid030 :
      Shard146.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard146.root_eq_path] using Shard146.valid
  have hvalid031 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid029 hvalid030
  have hvalid032 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid026 hvalid031
  have hvalid033 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid023 hvalid032
  have hvalid034 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid016 hvalid033
  simpa only [tree] using hvalid034

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
      (169861201307451064707723 / 819200000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard129.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (20103045611949021950217 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard129.root_eq_path] using Shard129.replay
  have hreplay001 :
      Shard130.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (3336282756958497517323 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard130.root_eq_path] using Shard130.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (20103045611949021950217 / 4096000000000000000000000000 : Rat) + (3336282756958497517323 / 512000000000000000000000000 : Rat) = (46793307667617002088801 / 4096000000000000000000000000 : Rat))
  have hreplay003 :
      Shard131.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (4665725041901420309229 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard131.root_eq_path] using Shard131.replay
  have hreplay004 :
      Shard132.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (92640345451823451135087 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard132.root_eq_path] using Shard132.replay
  have hreplay005 :
      Shard133.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (48535330780828587856113 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard133.root_eq_path] using Shard133.replay
  have hraw006 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hreplay004 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (92640345451823451135087 / 16384000000000000000000000000 : Rat) + (48535330780828587856113 / 8192000000000000000000000000 : Rat) = (189711007013480626847313 / 16384000000000000000000000000 : Rat))
  have hraw007 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay003 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (4665725041901420309229 / 512000000000000000000000000 : Rat) + (189711007013480626847313 / 16384000000000000000000000000 : Rat) = (339014208354326076742641 / 16384000000000000000000000000 : Rat))
  have hraw008 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (46793307667617002088801 / 4096000000000000000000000000 : Rat) + (339014208354326076742641 / 16384000000000000000000000000 : Rat) = (105237487804958817019569 / 3276800000000000000000000000 : Rat))
  have hreplay009 :
      Shard134.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (2113148203425234544977 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard134.root_eq_path] using Shard134.replay
  have hreplay010 :
      Shard135.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (104574393759819078215919 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard135.root_eq_path] using Shard135.replay
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay009 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (2113148203425234544977 / 204800000000000000000000000 : Rat) + (104574393759819078215919 / 8192000000000000000000000000 : Rat) = (189100321896828460014999 / 8192000000000000000000000000 : Rat))
  have hreplay012 :
      Shard136.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (51288117227947102352589 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard136.root_eq_path] using Shard136.replay
  have hreplay013 :
      Shard137.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (129857507120125122485733 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard137.root_eq_path] using Shard137.replay
  have hraw014 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay012 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (51288117227947102352589 / 4096000000000000000000000000 : Rat) + (129857507120125122485733 / 8192000000000000000000000000 : Rat) = (232433741576019327190911 / 8192000000000000000000000000 : Rat))
  have hraw015 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay011 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (189100321896828460014999 / 8192000000000000000000000000 : Rat) + (232433741576019327190911 / 8192000000000000000000000000 : Rat) = (42153406347284778720591 / 819200000000000000000000000 : Rat))
  have hraw016 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay008 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (105237487804958817019569 / 3276800000000000000000000000 : Rat) + (42153406347284778720591 / 819200000000000000000000000 : Rat) = (273851113194097931901933 / 3276800000000000000000000000 : Rat))
  have hreplay017 :
      Shard138.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (59734841603849013046311 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard138.root_eq_path] using Shard138.replay
  have hreplay018 :
      Shard139.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (26193460685542064375139 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard139.root_eq_path] using Shard139.replay
  have hraw019 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay017 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (59734841603849013046311 / 4096000000000000000000000000 : Rat) + (26193460685542064375139 / 2048000000000000000000000000 : Rat) = (112121762974933141796589 / 4096000000000000000000000000 : Rat))
  have hreplay020 :
      Shard140.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (27540115921344356322021 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard140.root_eq_path] using Shard140.replay
  have hreplay021 :
      Shard141.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (5553578437162209128709 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard141.root_eq_path] using Shard141.replay
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (27540115921344356322021 / 1638400000000000000000000000 : Rat) + (5553578437162209128709 / 327680000000000000000000000 : Rat) = (27654004053577700982783 / 819200000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay019 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (112121762974933141796589 / 4096000000000000000000000000 : Rat) + (27654004053577700982783 / 819200000000000000000000000 : Rat) = (31298972905352705838813 / 512000000000000000000000000 : Rat))
  have hreplay024 :
      Shard142.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (48890050568490216262149 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard142.root_eq_path] using Shard142.replay
  have hreplay025 :
      Shard143.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (125180088562348356014703 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard143.root_eq_path] using Shard143.replay
  have hraw026 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay024 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (48890050568490216262149 / 4096000000000000000000000000 : Rat) + (125180088562348356014703 / 8192000000000000000000000000 : Rat) = (222960189699328788539001 / 8192000000000000000000000000 : Rat))
  have hreplay027 :
      Shard144.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (67877779804881363145863 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard144.root_eq_path] using Shard144.replay
  have hreplay028 :
      Shard145.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (79264517458423680464949 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard145.root_eq_path] using Shard145.replay
  have hraw029 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay027 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (67877779804881363145863 / 8192000000000000000000000000 : Rat) + (79264517458423680464949 / 8192000000000000000000000000 : Rat) = (36785574315826260902703 / 2048000000000000000000000000 : Rat))
  have hreplay030 :
      Shard146.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (286196353281977383503153 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard146.root_eq_path] using Shard146.replay
  have hraw031 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay029 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (36785574315826260902703 / 2048000000000000000000000000 : Rat) + (286196353281977383503153 / 16384000000000000000000000000 : Rat) = (580480947808587470724777 / 16384000000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay026 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (222960189699328788539001 / 8192000000000000000000000000 : Rat) + (580480947808587470724777 / 16384000000000000000000000000 : Rat) = (1026401327207245047802779 / 16384000000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay023 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (31298972905352705838813 / 512000000000000000000000000 : Rat) + (1026401327207245047802779 / 16384000000000000000000000000 : Rat) = (405593692035706326928959 / 3276800000000000000000000000 : Rat))
  have hraw034 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay016 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (273851113194097931901933 / 3276800000000000000000000000 : Rat) + (405593692035706326928959 / 3276800000000000000000000000 : Rat) = (169861201307451064707723 / 819200000000000000000000000 : Rat))
  simpa only [tree] using hreplay034

end Branch007
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
