import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard061
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard062
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard063
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard064
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard065
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard066
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard067
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard068
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard069
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard070
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard071
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard072
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard073
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard074
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard075
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard076
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard077
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard078

/-!
# exact P2 forest branch Branch003
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch003

/- Root 0, exact path ((0, 'right'), (2, 'left'), (4, 'right')), 419 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard061.tree
          Shard062.tree
        )
        Shard063.tree
      )
      (.split (2 : Fin 6)
        Shard064.tree
        (.split (0 : Fin 6)
          Shard065.tree
          Shard066.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard067.tree
          Shard068.tree
        )
        (.split (1 : Fin 6)
          Shard069.tree
          (.split (0 : Fin 6)
            Shard070.tree
            Shard071.tree
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            Shard072.tree
            Shard073.tree
          )
          (.split (2 : Fin 6)
            Shard074.tree
            Shard075.tree
          )
        )
        (.split (4 : Fin 6)
          Shard076.tree
          (.split (3 : Fin 6)
            Shard077.tree
            Shard078.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard061.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard061.root_eq_path] using Shard061.valid
  have hvalid001 :
      Shard062.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard062.root_eq_path] using Shard062.valid
  have hvalid002 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard063.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard063.root_eq_path] using Shard063.valid
  have hvalid004 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid002 hvalid003
  have hvalid005 :
      Shard064.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard064.root_eq_path] using Shard064.valid
  have hvalid006 :
      Shard065.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard065.root_eq_path] using Shard065.valid
  have hvalid007 :
      Shard066.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard066.root_eq_path] using Shard066.valid
  have hvalid008 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard067.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard067.root_eq_path] using Shard067.valid
  have hvalid012 :
      Shard068.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard068.root_eq_path] using Shard068.valid
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard069.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard069.root_eq_path] using Shard069.valid
  have hvalid015 :
      Shard070.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard070.root_eq_path] using Shard070.valid
  have hvalid016 :
      Shard071.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard071.root_eq_path] using Shard071.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid014 hvalid017
  have hvalid019 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid013 hvalid018
  have hvalid020 :
      Shard072.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard072.root_eq_path] using Shard072.valid
  have hvalid021 :
      Shard073.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard073.root_eq_path] using Shard073.valid
  have hvalid022 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :
      Shard074.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard074.root_eq_path] using Shard074.valid
  have hvalid024 :
      Shard075.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard075.root_eq_path] using Shard075.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :
      Shard076.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard076.root_eq_path] using Shard076.valid
  have hvalid028 :
      Shard077.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard077.root_eq_path] using Shard077.valid
  have hvalid029 :
      Shard078.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard078.root_eq_path] using Shard078.valid
  have hvalid030 :=
    valid_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid027 hvalid030
  have hvalid032 :=
    valid_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid026 hvalid031
  have hvalid033 :=
    valid_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid019 hvalid032
  have hvalid034 :=
    valid_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid033
  simpa only [tree] using hvalid034

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (118076077766053126848447 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard061.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (1832032095725313859113 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard061.root_eq_path] using Shard061.replay
  have hreplay001 :
      Shard062.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (95825356286737887513 / 81920000000000000000000000 : Rat) := by
    simpa only [Shard062.root_eq_path] using Shard062.replay
  have hraw002 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (1832032095725313859113 / 819200000000000000000000000 : Rat) + (95825356286737887513 / 81920000000000000000000000 : Rat) = (2790285658592692734243 / 819200000000000000000000000 : Rat))
  have hreplay003 :
      Shard063.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (1112461865601978680811 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard063.root_eq_path] using Shard063.replay
  have hraw004 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay002 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (2790285658592692734243 / 819200000000000000000000000 : Rat) + (1112461865601978680811 / 204800000000000000000000000 : Rat) = (7240133121000607457487 / 819200000000000000000000000 : Rat))
  have hreplay005 :
      Shard064.tree.replayWeightRat (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2386207569733044431517 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard064.root_eq_path] using Shard064.replay
  have hreplay006 :
      Shard065.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (566411088377105908299 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard065.root_eq_path] using Shard065.replay
  have hreplay007 :
      Shard066.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (750217692787838855613 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard066.root_eq_path] using Shard066.replay
  have hraw008 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (566411088377105908299 / 204800000000000000000000000 : Rat) + (750217692787838855613 / 409600000000000000000000000 : Rat) = (1883039869542050672211 / 409600000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (2386207569733044431517 / 409600000000000000000000000 : Rat) + (1883039869542050672211 / 409600000000000000000000000 : Rat) = (266827964954693443983 / 25600000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (7240133121000607457487 / 819200000000000000000000000 : Rat) + (266827964954693443983 / 25600000000000000000000000 : Rat) = (15778627999550797664943 / 819200000000000000000000000 : Rat))
  have hreplay011 :
      Shard067.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (147917081325573394857 / 32768000000000000000000000 : Rat) := by
    simpa only [Shard067.root_eq_path] using Shard067.replay
  have hreplay012 :
      Shard068.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (472038734680420880907 / 81920000000000000000000000 : Rat) := by
    simpa only [Shard068.root_eq_path] using Shard068.replay
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (147917081325573394857 / 32768000000000000000000000 : Rat) + (472038734680420880907 / 81920000000000000000000000 : Rat) = (1683662875988708736099 / 163840000000000000000000000 : Rat))
  have hreplay014 :
      Shard069.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (834131548687923368289 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard069.root_eq_path] using Shard069.replay
  have hreplay015 :
      Shard070.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2231708750387765219637 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard070.root_eq_path] using Shard070.replay
  have hreplay016 :
      Shard071.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2852216970934663818783 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard071.root_eq_path] using Shard071.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (2231708750387765219637 / 819200000000000000000000000 : Rat) + (2852216970934663818783 / 1638400000000000000000000000 : Rat) = (7315634471710194258057 / 1638400000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay014 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (834131548687923368289 / 163840000000000000000000000 : Rat) + (7315634471710194258057 / 1638400000000000000000000000 : Rat) = (15656949958589427940947 / 1638400000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay013 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (1683662875988708736099 / 163840000000000000000000000 : Rat) + (15656949958589427940947 / 1638400000000000000000000000 : Rat) = (32493578718476515301937 / 1638400000000000000000000000 : Rat))
  have hreplay020 :
      Shard072.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (2466876441096854421921 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard072.root_eq_path] using Shard072.replay
  have hreplay021 :
      Shard073.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (1209113812419428620881 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard073.root_eq_path] using Shard073.replay
  have hraw022 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (2466876441096854421921 / 819200000000000000000000000 : Rat) + (1209113812419428620881 / 327680000000000000000000000 : Rat) = (10979321944290851948247 / 1638400000000000000000000000 : Rat))
  have hreplay023 :
      Shard074.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2912524213049732434131 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard074.root_eq_path] using Shard074.replay
  have hreplay024 :
      Shard075.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (543342232920487105611 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard075.root_eq_path] using Shard075.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (2912524213049732434131 / 819200000000000000000000000 : Rat) + (543342232920487105611 / 204800000000000000000000000 : Rat) = (203435725789267234263 / 32768000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (10979321944290851948247 / 1638400000000000000000000000 : Rat) + (203435725789267234263 / 32768000000000000000000000 : Rat) = (21151108233754213661397 / 1638400000000000000000000000 : Rat))
  have hreplay027 :
      Shard076.tree.replayWeightRat ((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1815043929417388827333 / 204800000000000000000000000 : Rat) := by
    simpa only [Shard076.root_eq_path] using Shard076.replay
  have hreplay028 :
      Shard077.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (2052143517547418705289 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard077.root_eq_path] using Shard077.replay
  have hreplay029 :
      Shard078.tree.replayWeightRat (((((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (10145209309192017115407 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard078.root_eq_path] using Shard078.replay
  have hraw030 :=
    replay_split (T := (((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (2052143517547418705289 / 409600000000000000000000000 : Rat) + (10145209309192017115407 / 1638400000000000000000000000 : Rat) = (18353783379381691936563 / 1638400000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay027 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (1815043929417388827333 / 204800000000000000000000000 : Rat) + (18353783379381691936563 / 1638400000000000000000000000 : Rat) = (32874134814720802555227 / 1638400000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := (((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay026 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (21151108233754213661397 / 1638400000000000000000000000 : Rat) + (32874134814720802555227 / 1638400000000000000000000000 : Rat) = (3376577690529688513539 / 102400000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := ((((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay019 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (32493578718476515301937 / 1638400000000000000000000000 : Rat) + (3376577690529688513539 / 102400000000000000000000000 : Rat) = (86518821766951531518561 / 1638400000000000000000000000 : Rat))
  have hraw034 :=
    replay_split (T := (((sectionSixP2RootD974 (0 : Fin 3)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (15778627999550797664943 / 819200000000000000000000000 : Rat) + (86518821766951531518561 / 1638400000000000000000000000 : Rat) = (118076077766053126848447 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay034

end Branch003
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
