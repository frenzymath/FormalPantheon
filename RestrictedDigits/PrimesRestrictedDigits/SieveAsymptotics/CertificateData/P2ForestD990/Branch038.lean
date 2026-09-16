import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard626
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard627
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard628
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard629
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard630
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard631
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard632
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard633
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard634
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard635
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard636
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard637
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard638
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard639
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard640
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard641
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard642
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard643
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard644

/-!
# exact P2 forest branch Branch038
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch038

/- Root 2, exact path ((2, 'right'), (1, 'right'), (2, 'left'), (4, 'left')), 393 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            Shard626.tree
            Shard627.tree
          )
          (.split (2 : Fin 6)
            Shard628.tree
            Shard629.tree
          )
        )
        (.split (5 : Fin 6)
          Shard630.tree
          Shard631.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard632.tree
          (.split (3 : Fin 6)
            Shard633.tree
            Shard634.tree
          )
        )
        (.split (5 : Fin 6)
          Shard635.tree
          (.split (1 : Fin 6)
            Shard636.tree
            Shard637.tree
          )
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard638.tree
          Shard639.tree
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            Shard640.tree
            Shard641.tree
          )
          Shard642.tree
        )
      )
      (.split (3 : Fin 6)
        Shard643.tree
        Shard644.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard626.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard626.root_eq_path] using Shard626.valid
  have hvalid001 :
      Shard627.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard627.root_eq_path] using Shard627.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard628.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard628.root_eq_path] using Shard628.valid
  have hvalid004 :
      Shard629.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard629.root_eq_path] using Shard629.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard630.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard630.root_eq_path] using Shard630.valid
  have hvalid008 :
      Shard631.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard631.root_eq_path] using Shard631.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid009
  have hvalid011 :
      Shard632.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard632.root_eq_path] using Shard632.valid
  have hvalid012 :
      Shard633.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard633.root_eq_path] using Shard633.valid
  have hvalid013 :
      Shard634.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard634.root_eq_path] using Shard634.valid
  have hvalid014 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid012 hvalid013
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid011 hvalid014
  have hvalid016 :
      Shard635.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard635.root_eq_path] using Shard635.valid
  have hvalid017 :
      Shard636.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard636.root_eq_path] using Shard636.valid
  have hvalid018 :
      Shard637.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard637.root_eq_path] using Shard637.valid
  have hvalid019 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid017 hvalid018
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid016 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid020
  have hvalid022 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid021
  have hvalid023 :
      Shard638.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard638.root_eq_path] using Shard638.valid
  have hvalid024 :
      Shard639.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard639.root_eq_path] using Shard639.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :
      Shard640.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard640.root_eq_path] using Shard640.valid
  have hvalid027 :
      Shard641.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard641.root_eq_path] using Shard641.valid
  have hvalid028 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid026 hvalid027
  have hvalid029 :
      Shard642.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard642.root_eq_path] using Shard642.valid
  have hvalid030 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid025 hvalid030
  have hvalid032 :
      Shard643.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard643.root_eq_path] using Shard643.valid
  have hvalid033 :
      Shard644.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard644.root_eq_path] using Shard644.valid
  have hvalid034 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid032 hvalid033
  have hvalid035 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid031 hvalid034
  have hvalid036 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid022 hvalid035
  simpa only [tree] using hvalid036

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (5836753972903449215310867 / 4096000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard626.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (126385065968028353580987 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard626.root_eq_path] using Shard626.replay
  have hreplay001 :
      Shard627.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (127217982562774396825653 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard627.root_eq_path] using Shard627.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (126385065968028353580987 / 4096000000000000000000000000 : Rat) + (127217982562774396825653 / 4096000000000000000000000000 : Rat) = (3170038106635034380083 / 51200000000000000000000000 : Rat))
  have hreplay003 :
      Shard628.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (131296917753260540958051 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard628.root_eq_path] using Shard628.replay
  have hreplay004 :
      Shard629.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (67119947297248339687797 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard629.root_eq_path] using Shard629.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (131296917753260540958051 / 4096000000000000000000000000 : Rat) + (67119947297248339687797 / 2048000000000000000000000000 : Rat) = (53107362469551444066729 / 819200000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (3170038106635034380083 / 51200000000000000000000000 : Rat) + (53107362469551444066729 / 819200000000000000000000000 : Rat) = (103827972175711994148057 / 819200000000000000000000000 : Rat))
  have hreplay007 :
      Shard630.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (738461735219067108069483 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard630.root_eq_path] using Shard630.replay
  have hreplay008 :
      Shard631.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (937043155984959644098077 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard631.root_eq_path] using Shard631.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (738461735219067108069483 / 8192000000000000000000000000 : Rat) + (937043155984959644098077 / 8192000000000000000000000000 : Rat) = (41887622280100668804189 / 204800000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (103827972175711994148057 / 819200000000000000000000000 : Rat) + (41887622280100668804189 / 204800000000000000000000000 : Rat) = (271378461296114669364813 / 819200000000000000000000000 : Rat))
  have hreplay011 :
      Shard632.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (132176120614698257305137 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard632.root_eq_path] using Shard632.replay
  have hreplay012 :
      Shard633.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (260797158946369232330661 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard633.root_eq_path] using Shard633.replay
  have hreplay013 :
      Shard634.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (170565345480164042363913 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard634.root_eq_path] using Shard634.replay
  have hraw014 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay012 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (260797158946369232330661 / 4096000000000000000000000000 : Rat) + (170565345480164042363913 / 4096000000000000000000000000 : Rat) = (215681252213266637347287 / 2048000000000000000000000000 : Rat))
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay011 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (132176120614698257305137 / 2048000000000000000000000000 : Rat) + (215681252213266637347287 / 2048000000000000000000000000 : Rat) = (43482171603495611831553 / 256000000000000000000000000 : Rat))
  have hreplay016 :
      Shard635.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (266731390854465335947503 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard635.root_eq_path] using Shard635.replay
  have hreplay017 :
      Shard636.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1059216946272233457550803 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard636.root_eq_path] using Shard636.replay
  have hreplay018 :
      Shard637.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4397020675505091745929 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard637.root_eq_path] using Shard637.replay
  have hraw019 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay017 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (1059216946272233457550803 / 16384000000000000000000000000 : Rat) + (4397020675505091745929 / 102400000000000000000000000 : Rat) = (1762740254353048136899443 / 16384000000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay016 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (266731390854465335947503 / 4096000000000000000000000000 : Rat) + (1762740254353048136899443 / 16384000000000000000000000000 : Rat) = (565933163554181896137891 / 3276800000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (43482171603495611831553 / 256000000000000000000000000 : Rat) + (565933163554181896137891 / 3276800000000000000000000000 : Rat) = (5612524800394628637908847 / 16384000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (271378461296114669364813 / 819200000000000000000000000 : Rat) + (5612524800394628637908847 / 16384000000000000000000000000 : Rat) = (11040094026316922025205107 / 16384000000000000000000000000 : Rat))
  have hreplay023 :
      Shard638.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (586871113976155101816189 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard638.root_eq_path] using Shard638.replay
  have hreplay024 :
      Shard639.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (141363691095048698935233 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard639.root_eq_path] using Shard639.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (586871113976155101816189 / 8192000000000000000000000000 : Rat) + (141363691095048698935233 / 2048000000000000000000000000 : Rat) = (1152325878356349897557121 / 8192000000000000000000000000 : Rat))
  have hreplay026 :
      Shard640.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1295634189392518333151727 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard640.root_eq_path] using Shard640.replay
  have hreplay027 :
      Shard641.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (465575041732309440691779 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard641.root_eq_path] using Shard641.replay
  have hraw028 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay026 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (1295634189392518333151727 / 16384000000000000000000000000 : Rat) + (465575041732309440691779 / 8192000000000000000000000000 : Rat) = (445356854571427442907057 / 3276800000000000000000000000 : Rat))
  have hreplay029 :
      Shard642.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (726791369903441624081619 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard642.root_eq_path] using Shard642.replay
  have hraw030 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (445356854571427442907057 / 3276800000000000000000000000 : Rat) + (726791369903441624081619 / 8192000000000000000000000000 : Rat) = (3680367012664020462698523 / 16384000000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay025 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (1152325878356349897557121 / 8192000000000000000000000000 : Rat) + (3680367012664020462698523 / 16384000000000000000000000000 : Rat) = (1197003753875344051562553 / 3276800000000000000000000000 : Rat))
  have hreplay032 :
      Shard643.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (989247220923538582280397 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard643.root_eq_path] using Shard643.replay
  have hreplay033 :
      Shard644.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (295614276528250031138001 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard644.root_eq_path] using Shard644.replay
  have hraw034 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay032 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (989247220923538582280397 / 4096000000000000000000000000 : Rat) + (295614276528250031138001 / 2048000000000000000000000000 : Rat) = (1580475773980038644556399 / 4096000000000000000000000000 : Rat))
  have hraw035 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay031 hreplay034
  have hreplay035 := hraw035.trans
    (by norm_num : (1197003753875344051562553 / 3276800000000000000000000000 : Rat) + (1580475773980038644556399 / 4096000000000000000000000000 : Rat) = (12306921865296874836038361 / 16384000000000000000000000000 : Rat))
  have hraw036 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay022 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (11040094026316922025205107 / 16384000000000000000000000000 : Rat) + (12306921865296874836038361 / 16384000000000000000000000000 : Rat) = (5836753972903449215310867 / 4096000000000000000000000000 : Rat))
  simpa only [tree] using hreplay036

end Branch038
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
