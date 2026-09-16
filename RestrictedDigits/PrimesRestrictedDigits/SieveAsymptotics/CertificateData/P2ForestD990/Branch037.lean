import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard610
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard611
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard612
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard613
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard614
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard615
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard616
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard617
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard618
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard619
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard620
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard621
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard622
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard623
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard624
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard625

/-!
# exact P2 forest branch Branch037
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch037

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'right'), (4, 'right')), 345 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (3 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard610.tree
          (.split (1 : Fin 6)
            Shard611.tree
            Shard612.tree
          )
        )
        (.split (3 : Fin 6)
          Shard613.tree
          (.split (3 : Fin 6)
            Shard614.tree
            Shard615.tree
          )
        )
      )
      (.split (0 : Fin 6)
        (.split (4 : Fin 6)
          Shard616.tree
          Shard617.tree
        )
        (.split (2 : Fin 6)
          Shard618.tree
          Shard619.tree
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        Shard620.tree
        Shard621.tree
      )
      (.split (4 : Fin 6)
        (.split (1 : Fin 6)
          Shard622.tree
          Shard623.tree
        )
        (.split (1 : Fin 6)
          Shard624.tree
          Shard625.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard610.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard610.root_eq_path] using Shard610.valid
  have hvalid001 :
      Shard611.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard611.root_eq_path] using Shard611.valid
  have hvalid002 :
      Shard612.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard612.root_eq_path] using Shard612.valid
  have hvalid003 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard613.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard613.root_eq_path] using Shard613.valid
  have hvalid006 :
      Shard614.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard614.root_eq_path] using Shard614.valid
  have hvalid007 :
      Shard615.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard615.root_eq_path] using Shard615.valid
  have hvalid008 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard616.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard616.root_eq_path] using Shard616.valid
  have hvalid012 :
      Shard617.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard617.root_eq_path] using Shard617.valid
  have hvalid013 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid011 hvalid012
  have hvalid014 :
      Shard618.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard618.root_eq_path] using Shard618.valid
  have hvalid015 :
      Shard619.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard619.root_eq_path] using Shard619.valid
  have hvalid016 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid017
  have hvalid019 :
      Shard620.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard620.root_eq_path] using Shard620.valid
  have hvalid020 :
      Shard621.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard621.root_eq_path] using Shard621.valid
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid019 hvalid020
  have hvalid022 :
      Shard622.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard622.root_eq_path] using Shard622.valid
  have hvalid023 :
      Shard623.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard623.root_eq_path] using Shard623.valid
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :
      Shard624.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard624.root_eq_path] using Shard624.valid
  have hvalid026 :
      Shard625.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard625.root_eq_path] using Shard625.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid024 hvalid027
  have hvalid029 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid021 hvalid028
  have hvalid030 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid018 hvalid029
  simpa only [tree] using hvalid030

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (16916013883555292440369431 / 8192000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard610.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (447641484072448137793659 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard610.root_eq_path] using Shard610.replay
  have hreplay001 :
      Shard611.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (72448087070215220063571 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard611.root_eq_path] using Shard611.replay
  have hreplay002 :
      Shard612.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (710448893341145094393441 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard612.root_eq_path] using Shard612.replay
  have hraw003 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (72448087070215220063571 / 1024000000000000000000000000 : Rat) + (710448893341145094393441 / 8192000000000000000000000000 : Rat) = (1290033589902866854902009 / 8192000000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (447641484072448137793659 / 4096000000000000000000000000 : Rat) + (1290033589902866854902009 / 8192000000000000000000000000 : Rat) = (2185316558047763130489327 / 8192000000000000000000000000 : Rat))
  have hreplay005 :
      Shard613.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (88551199942936718185143 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard613.root_eq_path] using Shard613.replay
  have hreplay006 :
      Shard614.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (173737717552688270440689 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard614.root_eq_path] using Shard614.replay
  have hreplay007 :
      Shard615.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (686258625604669519083579 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard615.root_eq_path] using Shard615.replay
  have hraw008 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (173737717552688270440689 / 2048000000000000000000000000 : Rat) + (686258625604669519083579 / 8192000000000000000000000000 : Rat) = (276241899163084520169267 / 1638400000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (88551199942936718185143 / 512000000000000000000000000 : Rat) + (276241899163084520169267 / 1638400000000000000000000000 : Rat) = (2798028694902410091808623 / 8192000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (2185316558047763130489327 / 8192000000000000000000000000 : Rat) + (2798028694902410091808623 / 8192000000000000000000000000 : Rat) = (99666905059003464445959 / 163840000000000000000000000 : Rat))
  have hreplay011 :
      Shard616.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (234278946278356423789413 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard616.root_eq_path] using Shard616.replay
  have hreplay012 :
      Shard617.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (576393963940033600253139 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard617.root_eq_path] using Shard617.replay
  have hraw013 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay011 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (234278946278356423789413 / 2048000000000000000000000000 : Rat) + (576393963940033600253139 / 4096000000000000000000000000 : Rat) = (208990371299349289566393 / 819200000000000000000000000 : Rat))
  have hreplay014 :
      Shard618.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (516813072897413215681443 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard618.root_eq_path] using Shard618.replay
  have hreplay015 :
      Shard619.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (730828705736481338766501 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard619.root_eq_path] using Shard619.replay
  have hraw016 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (516813072897413215681443 / 4096000000000000000000000000 : Rat) + (730828705736481338766501 / 4096000000000000000000000000 : Rat) = (155955222329236819305993 / 512000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (208990371299349289566393 / 819200000000000000000000000 : Rat) + (155955222329236819305993 / 512000000000000000000000000 : Rat) = (2292593635130641002279909 / 4096000000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (99666905059003464445959 / 163840000000000000000000000 : Rat) + (2292593635130641002279909 / 4096000000000000000000000000 : Rat) = (1196066565401431903357221 / 1024000000000000000000000000 : Rat))
  have hreplay019 :
      Shard620.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (177395527526654636227449 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard620.root_eq_path] using Shard620.replay
  have hreplay020 :
      Shard621.tree.replayWeightRat ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (708938115807136219106949 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard621.root_eq_path] using Shard621.replay
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay019 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (177395527526654636227449 / 1024000000000000000000000000 : Rat) + (708938115807136219106949 / 4096000000000000000000000000 : Rat) = (283704045182750952803349 / 819200000000000000000000000 : Rat))
  have hreplay022 :
      Shard622.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (443313511109865543500829 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard622.root_eq_path] using Shard622.replay
  have hreplay023 :
      Shard623.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1097919551373588968876739 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard623.root_eq_path] using Shard623.replay
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (443313511109865543500829 / 4096000000000000000000000000 : Rat) + (1097919551373588968876739 / 8192000000000000000000000000 : Rat) = (1984546573593320055878397 / 8192000000000000000000000000 : Rat))
  have hreplay025 :
      Shard624.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (286941454909435349602461 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard624.root_eq_path] using Shard624.replay
  have hreplay026 :
      Shard625.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (344532128821316557797483 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard625.root_eq_path] using Shard625.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (286941454909435349602461 / 2048000000000000000000000000 : Rat) + (344532128821316557797483 / 2048000000000000000000000000 : Rat) = (78934197966343988424993 / 256000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay024 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (1984546573593320055878397 / 8192000000000000000000000000 : Rat) + (78934197966343988424993 / 256000000000000000000000000 : Rat) = (4510440908516327685478173 / 8192000000000000000000000000 : Rat))
  have hraw029 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay021 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (283704045182750952803349 / 819200000000000000000000000 : Rat) + (4510440908516327685478173 / 8192000000000000000000000000 : Rat) = (7347481360343837213511663 / 8192000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay018 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (1196066565401431903357221 / 1024000000000000000000000000 : Rat) + (7347481360343837213511663 / 8192000000000000000000000000 : Rat) = (16916013883555292440369431 / 8192000000000000000000000000 : Rat))
  simpa only [tree] using hreplay030

end Branch037
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
