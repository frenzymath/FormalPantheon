import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard030
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard031
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard032
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard033
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard034
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard035
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard036
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard037
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard038
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard039
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard040
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard041
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard042
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard043
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard044

/-!
# exact P0 forest branch Branch002
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch002

/- Root 0, exact path ((1, 'right'), (0, 'right')), 1215 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (2 : Fin 6)
    (.split (4 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard030.tree
          Shard031.tree
        )
        (.split (0 : Fin 6)
          Shard032.tree
          Shard033.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard034.tree
          Shard035.tree
        )
        (.split (3 : Fin 6)
          Shard036.tree
          Shard037.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (1 : Fin 6)
        Shard038.tree
        (.split (0 : Fin 6)
          Shard039.tree
          Shard040.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          Shard041.tree
          Shard042.tree
        )
        (.split (2 : Fin 6)
          Shard043.tree
          Shard044.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard030.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard030.root_eq_path] using Shard030.valid
  have hvalid001 :
      Shard031.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard031.root_eq_path] using Shard031.valid
  have hvalid002 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard032.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard032.root_eq_path] using Shard032.valid
  have hvalid004 :
      Shard033.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard033.root_eq_path] using Shard033.valid
  have hvalid005 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard034.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard034.root_eq_path] using Shard034.valid
  have hvalid008 :
      Shard035.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard035.root_eq_path] using Shard035.valid
  have hvalid009 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard036.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard036.root_eq_path] using Shard036.valid
  have hvalid011 :
      Shard037.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard037.root_eq_path] using Shard037.valid
  have hvalid012 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard038.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard038.root_eq_path] using Shard038.valid
  have hvalid016 :
      Shard039.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard039.root_eq_path] using Shard039.valid
  have hvalid017 :
      Shard040.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard040.root_eq_path] using Shard040.valid
  have hvalid018 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard041.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard041.root_eq_path] using Shard041.valid
  have hvalid021 :
      Shard042.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard042.root_eq_path] using Shard042.valid
  have hvalid022 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :
      Shard043.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard043.root_eq_path] using Shard043.valid
  have hvalid024 :
      Shard044.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard044.root_eq_path] using Shard044.valid
  have hvalid025 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid019 hvalid026
  have hvalid028 :=
    valid_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid014 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
      (9707856347510990129524979 / 1228800000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard030.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ q => q) =
        (3048092440630340611785829 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard030.root_eq_path] using Shard030.replay
  have hreplay001 :
      Shard031.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ q => q) =
        (420596372372905975796663 / 983040000000000000000000000 : Rat) := by
    simpa only [Shard031.root_eq_path] using Shard031.replay
  have hraw002 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (3048092440630340611785829 / 9830400000000000000000000000 : Rat) + (420596372372905975796663 / 983040000000000000000000000 : Rat) = (2418018721453133456584153 / 3276800000000000000000000000 : Rat))
  have hreplay003 :
      Shard032.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (868477971667487052807703 / 1966080000000000000000000000 : Rat) := by
    simpa only [Shard032.root_eq_path] using Shard032.replay
  have hreplay004 :
      Shard033.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (76883935539709667944909 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard033.root_eq_path] using Shard033.replay
  have hraw005 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (868477971667487052807703 / 1966080000000000000000000000 : Rat) + (76883935539709667944909 / 163840000000000000000000000 : Rat) = (1791085198144003068146611 / 1966080000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (2418018721453133456584153 / 3276800000000000000000000000 : Rat) + (1791085198144003068146611 / 1966080000000000000000000000 : Rat) = (8104741077539707855242757 / 4915200000000000000000000000 : Rat))
  have hreplay007 :
      Shard034.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ q => q) =
        (4556979311189536733700839 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard034.root_eq_path] using Shard034.replay
  have hreplay008 :
      Shard035.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ q => q) =
        (487962987722147105967377 / 983040000000000000000000000 : Rat) := by
    simpa only [Shard035.root_eq_path] using Shard035.replay
  have hraw009 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (4556979311189536733700839 / 9830400000000000000000000000 : Rat) + (487962987722147105967377 / 983040000000000000000000000 : Rat) = (9436609188411007793374609 / 9830400000000000000000000000 : Rat))
  have hreplay010 :
      Shard036.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (2479189912905828170761339 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard036.root_eq_path] using Shard036.replay
  have hreplay011 :
      Shard037.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (3 : Fin 6)) (fun _ q => q) =
        (1634540712949037180687899 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard037.root_eq_path] using Shard037.replay
  have hraw012 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (2479189912905828170761339 / 4915200000000000000000000000 : Rat) + (1634540712949037180687899 / 3276800000000000000000000000 : Rat) = (78896015717270143068691 / 78643200000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (9436609188411007793374609 / 9830400000000000000000000000 : Rat) + (78896015717270143068691 / 78643200000000000000000000 : Rat) = (804108798044573986540041 / 409600000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (8104741077539707855242757 / 4915200000000000000000000000 : Rat) + (804108798044573986540041 / 409600000000000000000000000 : Rat) = (17754046654074595693723249 / 4915200000000000000000000000 : Rat))
  have hreplay015 :
      Shard038.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (2600543006179537684233419 / 2457600000000000000000000000 : Rat) := by
    simpa only [Shard038.root_eq_path] using Shard038.replay
  have hreplay016 :
      Shard039.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (208624267403003606622883 / 393216000000000000000000000 : Rat) := by
    simpa only [Shard039.root_eq_path] using Shard039.replay
  have hreplay017 :
      Shard040.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (1063394276743865127669863 / 1966080000000000000000000000 : Rat) := by
    simpa only [Shard040.root_eq_path] using Shard040.replay
  have hraw018 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (208624267403003606622883 / 393216000000000000000000000 : Rat) + (1063394276743865127669863 / 1966080000000000000000000000 : Rat) = (1053257806879441580392139 / 983040000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (2600543006179537684233419 / 2457600000000000000000000000 : Rat) + (1053257806879441580392139 / 983040000000000000000000000 : Rat) = (10467375046756283270427533 / 4915200000000000000000000000 : Rat))
  have hreplay020 :
      Shard041.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (1770157549573590632195153 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard041.root_eq_path] using Shard041.replay
  have hreplay021 :
      Shard042.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ q => q) =
        (5229975214224496838169431 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard042.root_eq_path] using Shard042.replay
  have hraw022 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (1770157549573590632195153 / 3276800000000000000000000000 : Rat) + (5229975214224496838169431 / 9830400000000000000000000000 : Rat) = (1054044786294526873475489 / 983040000000000000000000000 : Rat))
  have hreplay023 :
      Shard043.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (1756803847166504269552103 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard043.root_eq_path] using Shard043.replay
  have hreplay024 :
      Shard044.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (5409147973981381564487069 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard044.root_eq_path] using Shard044.replay
  have hraw025 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (1756803847166504269552103 / 3276800000000000000000000000 : Rat) + (5409147973981381564487069 / 9830400000000000000000000000 : Rat) = (5339779757740447186571689 / 4915200000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (1054044786294526873475489 / 983040000000000000000000000 : Rat) + (5339779757740447186571689 / 4915200000000000000000000000 : Rat) = (5305001844606540776974567 / 2457600000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay019 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (10467375046756283270427533 / 4915200000000000000000000000 : Rat) + (5305001844606540776974567 / 2457600000000000000000000000 : Rat) = (21077378735969364824376667 / 4915200000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay014 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (17754046654074595693723249 / 4915200000000000000000000000 : Rat) + (21077378735969364824376667 / 4915200000000000000000000000 : Rat) = (9707856347510990129524979 / 1228800000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch002
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
