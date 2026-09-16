import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard512
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard513
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard514
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard515
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard516
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard517
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard518
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard519
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard520
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard521
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard522
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard523
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard524
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard525
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard526
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard527
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard528

/-!
# exact P2 forest branch Branch031
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch031

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'right'), (4, 'right')), 377 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (0 : Fin 6)
    (.split (3 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (5 : Fin 6)
            Shard512.tree
            Shard513.tree
          )
          Shard514.tree
        )
        Shard515.tree
      )
      (.split (4 : Fin 6)
        Shard516.tree
        Shard517.tree
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard518.tree
          Shard519.tree
        )
        (.split (0 : Fin 6)
          Shard520.tree
          Shard521.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard522.tree
          (.split (5 : Fin 6)
            Shard523.tree
            Shard524.tree
          )
        )
        (.split (0 : Fin 6)
          (.split (0 : Fin 6)
            Shard525.tree
            Shard526.tree
          )
          (.split (2 : Fin 6)
            Shard527.tree
            Shard528.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard512.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard512.root_eq_path] using Shard512.valid
  have hvalid001 :
      Shard513.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard513.root_eq_path] using Shard513.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard514.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard514.root_eq_path] using Shard514.valid
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid003
  have hvalid005 :
      Shard515.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard515.root_eq_path] using Shard515.valid
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid004 hvalid005
  have hvalid007 :
      Shard516.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard516.root_eq_path] using Shard516.valid
  have hvalid008 :
      Shard517.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard517.root_eq_path] using Shard517.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid006 hvalid009
  have hvalid011 :
      Shard518.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard518.root_eq_path] using Shard518.valid
  have hvalid012 :
      Shard519.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard519.root_eq_path] using Shard519.valid
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard520.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard520.root_eq_path] using Shard520.valid
  have hvalid015 :
      Shard521.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard521.root_eq_path] using Shard521.valid
  have hvalid016 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :
      Shard522.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard522.root_eq_path] using Shard522.valid
  have hvalid019 :
      Shard523.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard523.root_eq_path] using Shard523.valid
  have hvalid020 :
      Shard524.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard524.root_eq_path] using Shard524.valid
  have hvalid021 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid019 hvalid020
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid018 hvalid021
  have hvalid023 :
      Shard525.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard525.root_eq_path] using Shard525.valid
  have hvalid024 :
      Shard526.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard526.root_eq_path] using Shard526.valid
  have hvalid025 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :
      Shard527.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard527.root_eq_path] using Shard527.valid
  have hvalid027 :
      Shard528.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard528.root_eq_path] using Shard528.valid
  have hvalid028 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid026 hvalid027
  have hvalid029 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid025 hvalid028
  have hvalid030 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid022 hvalid029
  have hvalid031 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid017 hvalid030
  have hvalid032 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid010 hvalid031
  simpa only [tree] using hvalid032

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (3909825496749259046611089 / 3276800000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard512.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (206259121517738560494813 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard512.root_eq_path] using Shard512.replay
  have hreplay001 :
      Shard513.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (141753553972817678440209 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard513.root_eq_path] using Shard513.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (206259121517738560494813 / 4096000000000000000000000000 : Rat) + (141753553972817678440209 / 2048000000000000000000000000 : Rat) = (489766229463373917375231 / 4096000000000000000000000000 : Rat))
  have hreplay003 :
      Shard514.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (87288653076109773794523 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard514.root_eq_path] using Shard514.replay
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (489766229463373917375231 / 4096000000000000000000000000 : Rat) + (87288653076109773794523 / 1024000000000000000000000000 : Rat) = (838920841767813012553323 / 4096000000000000000000000000 : Rat))
  have hreplay005 :
      Shard515.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (362240041249847393606331 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard515.root_eq_path] using Shard515.replay
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay004 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (838920841767813012553323 / 4096000000000000000000000000 : Rat) + (362240041249847393606331 / 2048000000000000000000000000 : Rat) = (312680184853501559953197 / 819200000000000000000000000 : Rat))
  have hreplay007 :
      Shard516.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (237893008690634081576823 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard516.root_eq_path] using Shard516.replay
  have hreplay008 :
      Shard517.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (46293839038492627655709 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard517.root_eq_path] using Shard517.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (237893008690634081576823 / 2048000000000000000000000000 : Rat) + (46293839038492627655709 / 409600000000000000000000000 : Rat) = (58670275485387152481921 / 256000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay006 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (312680184853501559953197 / 819200000000000000000000000 : Rat) + (58670275485387152481921 / 256000000000000000000000000 : Rat) = (2502125332033702239476721 / 4096000000000000000000000000 : Rat))
  have hreplay011 :
      Shard518.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (59553556701964954975233 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard518.root_eq_path] using Shard518.replay
  have hreplay012 :
      Shard519.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (434415602107234268460639 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard519.root_eq_path] using Shard519.replay
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (59553556701964954975233 / 819200000000000000000000000 : Rat) + (434415602107234268460639 / 4096000000000000000000000000 : Rat) = (183045846404264760834201 / 1024000000000000000000000000 : Rat))
  have hreplay014 :
      Shard520.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (120019780477837129204341 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard520.root_eq_path] using Shard520.replay
  have hreplay015 :
      Shard521.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (479938469215587327856611 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard521.root_eq_path] using Shard521.replay
  have hraw016 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (120019780477837129204341 / 2048000000000000000000000000 : Rat) + (479938469215587327856611 / 8192000000000000000000000000 : Rat) = (38400703645077433786959 / 327680000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (183045846404264760834201 / 1024000000000000000000000000 : Rat) + (38400703645077433786959 / 327680000000000000000000000 : Rat) = (2424384362361053931347583 / 8192000000000000000000000000 : Rat))
  have hreplay018 :
      Shard522.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (231124113435733904035593 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard522.root_eq_path] using Shard522.replay
  have hreplay019 :
      Shard523.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (64775409233791445669133 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard523.root_eq_path] using Shard523.replay
  have hreplay020 :
      Shard524.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (388784087800973105154021 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard524.root_eq_path] using Shard524.replay
  have hraw021 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay019 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (64775409233791445669133 / 1638400000000000000000000000 : Rat) + (388784087800973105154021 / 8192000000000000000000000000 : Rat) = (356330566984965166749843 / 4096000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay018 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (231124113435733904035593 / 4096000000000000000000000000 : Rat) + (356330566984965166749843 / 4096000000000000000000000000 : Rat) = (146863670105174767696359 / 1024000000000000000000000000 : Rat))
  have hreplay023 :
      Shard525.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (296235134857817685500211 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard525.root_eq_path] using Shard525.replay
  have hreplay024 :
      Shard526.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (588433768478583704512299 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard526.root_eq_path] using Shard526.replay
  have hraw025 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (296235134857817685500211 / 8192000000000000000000000000 : Rat) + (588433768478583704512299 / 16384000000000000000000000000 : Rat) = (1180904038194219075512721 / 16384000000000000000000000000 : Rat))
  have hreplay026 :
      Shard527.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (290332144435761763962363 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard527.root_eq_path] using Shard527.replay
  have hreplay027 :
      Shard528.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (145117595535209881468551 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard528.root_eq_path] using Shard528.replay
  have hraw028 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay026 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (290332144435761763962363 / 8192000000000000000000000000 : Rat) + (145117595535209881468551 / 4096000000000000000000000000 : Rat) = (116113467101236305379893 / 1638400000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay025 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (1180904038194219075512721 / 16384000000000000000000000000 : Rat) + (116113467101236305379893 / 1638400000000000000000000000 : Rat) = (2342038709206582129311651 / 16384000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay022 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (146863670105174767696359 / 1024000000000000000000000000 : Rat) + (2342038709206582129311651 / 16384000000000000000000000000 : Rat) = (938371486177875682490679 / 3276800000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay017 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (2424384362361053931347583 / 8192000000000000000000000000 : Rat) + (938371486177875682490679 / 3276800000000000000000000000 : Rat) = (9540626155611486275148561 / 16384000000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay010 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (2502125332033702239476721 / 4096000000000000000000000000 : Rat) + (9540626155611486275148561 / 16384000000000000000000000000 : Rat) = (3909825496749259046611089 / 3276800000000000000000000000 : Rat))
  simpa only [tree] using hreplay032

end Branch031
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
