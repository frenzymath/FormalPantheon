import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard297
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard298
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard299
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard300
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard301
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard302
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard303
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard304
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard305
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard306
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard307
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard308
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard309
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard310
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard311
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard312
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard313
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard314
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard315
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard316

/-!
# exact P2 forest branch Branch018
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch018

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'left')), 411 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            (.split (1 : Fin 6)
              Shard297.tree
              Shard298.tree
            )
            (.split (4 : Fin 6)
              Shard299.tree
              Shard300.tree
            )
          )
          (.split (2 : Fin 6)
            Shard301.tree
            Shard302.tree
          )
        )
        (.split (4 : Fin 6)
          Shard303.tree
          Shard304.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            Shard305.tree
            Shard306.tree
          )
          Shard307.tree
        )
        (.split (1 : Fin 6)
          Shard308.tree
          Shard309.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          (.split (4 : Fin 6)
            Shard310.tree
            Shard311.tree
          )
          Shard312.tree
        )
        Shard313.tree
      )
      (.split (3 : Fin 6)
        (.split (0 : Fin 6)
          Shard314.tree
          Shard315.tree
        )
        Shard316.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard297.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard297.root_eq_path] using Shard297.valid
  have hvalid001 :
      Shard298.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard298.root_eq_path] using Shard298.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard299.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard299.root_eq_path] using Shard299.valid
  have hvalid004 :
      Shard300.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard300.root_eq_path] using Shard300.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard301.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard301.root_eq_path] using Shard301.valid
  have hvalid008 :
      Shard302.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard302.root_eq_path] using Shard302.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid006 hvalid009
  have hvalid011 :
      Shard303.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard303.root_eq_path] using Shard303.valid
  have hvalid012 :
      Shard304.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard304.root_eq_path] using Shard304.valid
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid013
  have hvalid015 :
      Shard305.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard305.root_eq_path] using Shard305.valid
  have hvalid016 :
      Shard306.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard306.root_eq_path] using Shard306.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard307.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard307.root_eq_path] using Shard307.valid
  have hvalid019 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid017 hvalid018
  have hvalid020 :
      Shard308.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard308.root_eq_path] using Shard308.valid
  have hvalid021 :
      Shard309.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard309.root_eq_path] using Shard309.valid
  have hvalid022 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid019 hvalid022
  have hvalid024 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid014 hvalid023
  have hvalid025 :
      Shard310.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard310.root_eq_path] using Shard310.valid
  have hvalid026 :
      Shard311.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard311.root_eq_path] using Shard311.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :
      Shard312.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard312.root_eq_path] using Shard312.valid
  have hvalid029 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid027 hvalid028
  have hvalid030 :
      Shard313.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard313.root_eq_path] using Shard313.valid
  have hvalid031 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid029 hvalid030
  have hvalid032 :
      Shard314.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard314.root_eq_path] using Shard314.valid
  have hvalid033 :
      Shard315.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard315.root_eq_path] using Shard315.valid
  have hvalid034 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid032 hvalid033
  have hvalid035 :
      Shard316.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard316.root_eq_path] using Shard316.valid
  have hvalid036 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid034 hvalid035
  have hvalid037 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid031 hvalid036
  have hvalid038 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid024 hvalid037
  simpa only [tree] using hvalid038

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
      (4639071488530620019576509 / 8192000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard297.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (22201750506364703408151 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard297.root_eq_path] using Shard297.replay
  have hreplay001 :
      Shard298.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (178316752890968545706991 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard298.root_eq_path] using Shard298.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (22201750506364703408151 / 2048000000000000000000000000 : Rat) + (178316752890968545706991 / 16384000000000000000000000000 : Rat) = (355930756941886172972199 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard299.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (4440581286814290723561 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard299.root_eq_path] using Shard299.replay
  have hreplay004 :
      Shard300.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (101750391206218364344191 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard300.root_eq_path] using Shard300.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (4440581286814290723561 / 512000000000000000000000000 : Rat) + (101750391206218364344191 / 8192000000000000000000000000 : Rat) = (172799691795247015921167 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (355930756941886172972199 / 16384000000000000000000000000 : Rat) + (172799691795247015921167 / 8192000000000000000000000000 : Rat) = (701530140532380204814533 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Shard301.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (282268286585176270037283 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard301.root_eq_path] using Shard301.replay
  have hreplay008 :
      Shard302.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (53008849225263980804463 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard302.root_eq_path] using Shard302.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (282268286585176270037283 / 16384000000000000000000000000 : Rat) + (53008849225263980804463 / 2048000000000000000000000000 : Rat) = (706339080387288116472987 / 16384000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay006 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (701530140532380204814533 / 16384000000000000000000000000 : Rat) + (706339080387288116472987 / 16384000000000000000000000000 : Rat) = (8799182630747927008047 / 102400000000000000000000000 : Rat))
  have hreplay011 :
      Shard303.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (66119025354748149881763 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard303.root_eq_path] using Shard303.replay
  have hreplay012 :
      Shard304.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (194081083899125710257351 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard304.root_eq_path] using Shard304.replay
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (66119025354748149881763 / 2048000000000000000000000000 : Rat) + (194081083899125710257351 / 4096000000000000000000000000 : Rat) = (326319134608622010020877 / 4096000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (8799182630747927008047 / 102400000000000000000000000 : Rat) + (326319134608622010020877 / 4096000000000000000000000000 : Rat) = (678286439838539090342757 / 4096000000000000000000000000 : Rat))
  have hreplay015 :
      Shard305.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (65109014011360608991407 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard305.root_eq_path] using Shard305.replay
  have hreplay016 :
      Shard306.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (4135706371462114739871 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard306.root_eq_path] using Shard306.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (65109014011360608991407 / 8192000000000000000000000000 : Rat) + (4135706371462114739871 / 256000000000000000000000000 : Rat) = (197451617898148280667279 / 8192000000000000000000000000 : Rat))
  have hreplay018 :
      Shard307.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (628919668831940685420147 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard307.root_eq_path] using Shard307.replay
  have hraw019 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay017 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (197451617898148280667279 / 8192000000000000000000000000 : Rat) + (628919668831940685420147 / 16384000000000000000000000000 : Rat) = (204764580925647449350941 / 3276800000000000000000000000 : Rat))
  have hreplay020 :
      Shard308.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (210639748388749413934239 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard308.root_eq_path] using Shard308.replay
  have hreplay021 :
      Shard309.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (106022125256670502729047 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard309.root_eq_path] using Shard309.replay
  have hraw022 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (210639748388749413934239 / 4096000000000000000000000000 : Rat) + (106022125256670502729047 / 2048000000000000000000000000 : Rat) = (422683998902090419392333 / 4096000000000000000000000000 : Rat))
  have hraw023 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay019 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (204764580925647449350941 / 3276800000000000000000000000 : Rat) + (422683998902090419392333 / 4096000000000000000000000000 : Rat) = (2714558900236598924324037 / 16384000000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay014 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (678286439838539090342757 / 4096000000000000000000000000 : Rat) + (2714558900236598924324037 / 16384000000000000000000000000 : Rat) = (1085540931918151057139013 / 3276800000000000000000000000 : Rat))
  have hreplay025 :
      Shard310.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (78783343719076488366333 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard310.root_eq_path] using Shard310.replay
  have hreplay026 :
      Shard311.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (5326111523292781206483 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard311.root_eq_path] using Shard311.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (78783343719076488366333 / 16384000000000000000000000000 : Rat) + (5326111523292781206483 / 1024000000000000000000000000 : Rat) = (164001128091760987670061 / 16384000000000000000000000000 : Rat))
  have hreplay028 :
      Shard312.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (23316966553221128161143 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard312.root_eq_path] using Shard312.replay
  have hraw029 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay027 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (164001128091760987670061 / 16384000000000000000000000000 : Rat) + (23316966553221128161143 / 1024000000000000000000000000 : Rat) = (537072592943299038248349 / 16384000000000000000000000000 : Rat))
  have hreplay030 :
      Shard313.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (69508917503174033374041 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard313.root_eq_path] using Shard313.replay
  have hraw031 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay029 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (537072592943299038248349 / 16384000000000000000000000000 : Rat) + (69508917503174033374041 / 1024000000000000000000000000 : Rat) = (329843054598816714446601 / 3276800000000000000000000000 : Rat))
  have hreplay032 :
      Shard314.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (36115699786665928265799 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard314.root_eq_path] using Shard314.replay
  have hreplay033 :
      Shard315.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (174356388490725965790999 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard315.root_eq_path] using Shard315.replay
  have hraw034 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay032 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (36115699786665928265799 / 1024000000000000000000000000 : Rat) + (174356388490725965790999 / 4096000000000000000000000000 : Rat) = (63763837527477935770839 / 819200000000000000000000000 : Rat))
  have hreplay035 :
      Shard316.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (115743286740855308226021 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard316.root_eq_path] using Shard316.replay
  have hraw036 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay034 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (63763837527477935770839 / 819200000000000000000000000 : Rat) + (115743286740855308226021 / 2048000000000000000000000000 : Rat) = (550305761119100295306237 / 4096000000000000000000000000 : Rat))
  have hraw037 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay031 hreplay036
  have hreplay037 := hraw037.trans
    (by norm_num : (329843054598816714446601 / 3276800000000000000000000000 : Rat) + (550305761119100295306237 / 4096000000000000000000000000 : Rat) = (3850438317470484753457953 / 16384000000000000000000000000 : Rat))
  have hraw038 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay024 hreplay037
  have hreplay038 := hraw038.trans
    (by norm_num : (1085540931918151057139013 / 3276800000000000000000000000 : Rat) + (3850438317470484753457953 / 16384000000000000000000000000 : Rat) = (4639071488530620019576509 / 8192000000000000000000000000 : Rat))
  simpa only [tree] using hreplay038

end Branch018
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
