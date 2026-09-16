import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard317
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard318
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard319
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard320
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard321
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard322
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard323
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard324
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard325
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard326

/-!
# exact P2 forest branch Branch019
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch019

/- Root 1, exact path ((1, 'right'), (2, 'right'), (1, 'right')), 195 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (2 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        Shard317.tree
        Shard318.tree
      )
      (.split (4 : Fin 6)
        Shard319.tree
        Shard320.tree
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard321.tree
          Shard322.tree
        )
        (.split (4 : Fin 6)
          Shard323.tree
          Shard324.tree
        )
      )
      (.split (2 : Fin 6)
        Shard325.tree
        Shard326.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
  have hvalid000 :
      Shard317.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard317.root_eq_path] using Shard317.valid
  have hvalid001 :
      Shard318.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard318.root_eq_path] using Shard318.valid
  have hvalid002 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard319.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard319.root_eq_path] using Shard319.valid
  have hvalid004 :
      Shard320.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard320.root_eq_path] using Shard320.valid
  have hvalid005 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard321.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard321.root_eq_path] using Shard321.valid
  have hvalid008 :
      Shard322.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard322.root_eq_path] using Shard322.valid
  have hvalid009 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard323.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard323.root_eq_path] using Shard323.valid
  have hvalid011 :
      Shard324.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard324.root_eq_path] using Shard324.valid
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :
      Shard325.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard325.root_eq_path] using Shard325.valid
  have hvalid015 :
      Shard326.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard326.root_eq_path] using Shard326.valid
  have hvalid016 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid013 hvalid016
  have hvalid018 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid017
  simpa only [tree] using hvalid018

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
      (546461399394898824026799 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard317.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (95293142931544242321429 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard317.root_eq_path] using Shard317.replay
  have hreplay001 :
      Shard318.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (1544228220638818501371 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard318.root_eq_path] using Shard318.replay
  have hraw002 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (95293142931544242321429 / 8192000000000000000000000000 : Rat) + (1544228220638818501371 / 102400000000000000000000000 : Rat) = (218831400582649722431109 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard319.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (13964945061621681214389 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard319.root_eq_path] using Shard319.replay
  have hreplay004 :
      Shard320.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (99325093013215238315079 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard320.root_eq_path] using Shard320.replay
  have hraw005 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (13964945061621681214389 / 256000000000000000000000000 : Rat) + (99325093013215238315079 / 2048000000000000000000000000 : Rat) = (211044653506188688030191 / 2048000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (218831400582649722431109 / 8192000000000000000000000000 : Rat) + (211044653506188688030191 / 2048000000000000000000000000 : Rat) = (1063010014607404474551873 / 8192000000000000000000000000 : Rat))
  have hreplay007 :
      Shard321.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (18914183234318845613223 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard321.root_eq_path] using Shard321.replay
  have hreplay008 :
      Shard322.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (172840115987865532190673 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard322.root_eq_path] using Shard322.replay
  have hraw009 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (18914183234318845613223 / 409600000000000000000000000 : Rat) + (172840115987865532190673 / 4096000000000000000000000000 : Rat) = (361981948331053988322903 / 4096000000000000000000000000 : Rat))
  have hreplay010 :
      Shard323.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (48980200721978430864531 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard323.root_eq_path] using Shard323.replay
  have hreplay011 :
      Shard324.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (108466341310255525367787 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard324.root_eq_path] using Shard324.replay
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (48980200721978430864531 / 2048000000000000000000000000 : Rat) + (108466341310255525367787 / 4096000000000000000000000000 : Rat) = (206426742754212387096849 / 4096000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (361981948331053988322903 / 4096000000000000000000000000 : Rat) + (206426742754212387096849 / 4096000000000000000000000000 : Rat) = (71051086385658296927469 / 512000000000000000000000000 : Rat))
  have hreplay014 :
      Shard325.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (57809655989827464659859 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard325.root_eq_path] using Shard325.replay
  have hreplay015 :
      Shard326.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (150620488118623518051591 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard326.root_eq_path] using Shard326.replay
  have hraw016 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (57809655989827464659859 / 2048000000000000000000000000 : Rat) + (150620488118623518051591 / 4096000000000000000000000000 : Rat) = (266239800098278447371309 / 4096000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay013 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (71051086385658296927469 / 512000000000000000000000000 : Rat) + (266239800098278447371309 / 4096000000000000000000000000 : Rat) = (834648491183544822791061 / 4096000000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (1063010014607404474551873 / 8192000000000000000000000000 : Rat) + (834648491183544822791061 / 4096000000000000000000000000 : Rat) = (546461399394898824026799 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay018

end Branch019
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
