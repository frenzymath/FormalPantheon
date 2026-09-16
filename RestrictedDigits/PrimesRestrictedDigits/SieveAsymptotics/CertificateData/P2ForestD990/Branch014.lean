import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard239
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard240
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard241
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard242
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard243
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard244
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard245
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard246
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard247
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard248
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard249
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard250
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard251
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard252
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard253
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard254

/-!
# exact P2 forest branch Branch014
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch014

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'left')), 307 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard239.tree
          Shard240.tree
        )
        (.split (5 : Fin 6)
          Shard241.tree
          Shard242.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (4 : Fin 6)
          Shard243.tree
          Shard244.tree
        )
        (.split (4 : Fin 6)
          Shard245.tree
          Shard246.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard247.tree
          Shard248.tree
        )
        (.split (4 : Fin 6)
          Shard249.tree
          Shard250.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard251.tree
          Shard252.tree
        )
        (.split (1 : Fin 6)
          Shard253.tree
          Shard254.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
  have hvalid000 :
      Shard239.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard239.root_eq_path] using Shard239.valid
  have hvalid001 :
      Shard240.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard240.root_eq_path] using Shard240.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard241.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard241.root_eq_path] using Shard241.valid
  have hvalid004 :
      Shard242.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard242.root_eq_path] using Shard242.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard243.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard243.root_eq_path] using Shard243.valid
  have hvalid008 :
      Shard244.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard244.root_eq_path] using Shard244.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard245.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard245.root_eq_path] using Shard245.valid
  have hvalid011 :
      Shard246.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard246.root_eq_path] using Shard246.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard247.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard247.root_eq_path] using Shard247.valid
  have hvalid016 :
      Shard248.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard248.root_eq_path] using Shard248.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard249.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard249.root_eq_path] using Shard249.valid
  have hvalid019 :
      Shard250.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard250.root_eq_path] using Shard250.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard251.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard251.root_eq_path] using Shard251.valid
  have hvalid023 :
      Shard252.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard252.root_eq_path] using Shard252.valid
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard253.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard253.root_eq_path] using Shard253.valid
  have hvalid026 :
      Shard254.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard254.root_eq_path] using Shard254.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
      (513842946225232601401857 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard239.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (6864925294636971770097 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard239.root_eq_path] using Shard239.replay
  have hreplay001 :
      Shard240.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (57179990030222459223 / 64000000000000000000000000 : Rat) := by
    simpa only [Shard240.root_eq_path] using Shard240.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (6864925294636971770097 / 8192000000000000000000000000 : Rat) + (57179990030222459223 / 64000000000000000000000000 : Rat) = (14183964018505446550641 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard241.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (16473759415752049020189 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard241.root_eq_path] using Shard241.replay
  have hreplay004 :
      Shard242.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (11596884324975746255799 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard242.root_eq_path] using Shard242.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (16473759415752049020189 / 8192000000000000000000000000 : Rat) + (11596884324975746255799 / 4096000000000000000000000000 : Rat) = (39667528065703541531787 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (14183964018505446550641 / 8192000000000000000000000000 : Rat) + (39667528065703541531787 / 8192000000000000000000000000 : Rat) = (13462873021052247020607 / 2048000000000000000000000000 : Rat))
  have hreplay007 :
      Shard243.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (16583853685282060735161 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard243.root_eq_path] using Shard243.replay
  have hreplay008 :
      Shard244.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1244417847496762129047 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard244.root_eq_path] using Shard244.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (16583853685282060735161 / 8192000000000000000000000000 : Rat) + (1244417847496762129047 / 409600000000000000000000000 : Rat) = (41472210635217303316101 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Shard245.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (8183264777757927555687 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard245.root_eq_path] using Shard245.replay
  have hreplay011 :
      Shard246.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (19802091609165467502207 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard246.root_eq_path] using Shard246.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (8183264777757927555687 / 8192000000000000000000000000 : Rat) + (19802091609165467502207 / 16384000000000000000000000000 : Rat) = (36168621164681322613581 / 16384000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (41472210635217303316101 / 8192000000000000000000000000 : Rat) + (36168621164681322613581 / 16384000000000000000000000000 : Rat) = (119113042435115929245783 / 16384000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (13462873021052247020607 / 2048000000000000000000000000 : Rat) + (119113042435115929245783 / 16384000000000000000000000000 : Rat) = (226816026603533905410639 / 16384000000000000000000000000 : Rat))
  have hreplay015 :
      Shard247.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (3297867218188846334811 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard247.root_eq_path] using Shard247.replay
  have hreplay016 :
      Shard248.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7196361318125245624527 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard248.root_eq_path] using Shard248.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (3297867218188846334811 / 819200000000000000000000000 : Rat) + (7196361318125245624527 / 2048000000000000000000000000 : Rat) = (30882058727194722923109 / 4096000000000000000000000000 : Rat))
  have hreplay018 :
      Shard249.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (544631982115579331841 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard249.root_eq_path] using Shard249.replay
  have hreplay019 :
      Shard250.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (992505454422404911929 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard250.root_eq_path] using Shard250.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (544631982115579331841 / 256000000000000000000000000 : Rat) + (992505454422404911929 / 409600000000000000000000000 : Rat) = (9319583129036659214373 / 2048000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (30882058727194722923109 / 4096000000000000000000000000 : Rat) + (9319583129036659214373 / 2048000000000000000000000000 : Rat) = (9904244997053608270371 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard251.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (5015259024812465047641 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard251.root_eq_path] using Shard251.replay
  have hreplay023 :
      Shard252.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1316614905536719954923 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard252.root_eq_path] using Shard252.replay
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (5015259024812465047641 / 4096000000000000000000000000 : Rat) + (1316614905536719954923 / 1024000000000000000000000000 : Rat) = (10281718646959344867333 / 4096000000000000000000000000 : Rat))
  have hreplay025 :
      Shard253.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1676776134937665725109 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard253.root_eq_path] using Shard253.replay
  have hreplay026 :
      Shard254.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7139811197017918306143 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard254.root_eq_path] using Shard254.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (1676776134937665725109 / 819200000000000000000000000 : Rat) + (7139811197017918306143 / 8192000000000000000000000000 : Rat) = (23907572546394575557233 / 8192000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (10281718646959344867333 / 4096000000000000000000000000 : Rat) + (23907572546394575557233 / 8192000000000000000000000000 : Rat) = (44471009840313265291899 / 8192000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (9904244997053608270371 / 819200000000000000000000000 : Rat) + (44471009840313265291899 / 8192000000000000000000000000 : Rat) = (143513459810849347995609 / 8192000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (226816026603533905410639 / 16384000000000000000000000000 : Rat) + (143513459810849347995609 / 8192000000000000000000000000 : Rat) = (513842946225232601401857 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch014
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
