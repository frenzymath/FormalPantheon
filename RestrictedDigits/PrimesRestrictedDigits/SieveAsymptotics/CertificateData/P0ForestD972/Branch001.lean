import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0CertificateSupportD972
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ThreeRootCoverD971
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard015
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard016
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard017
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard018
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard019
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard020
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard021
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard022
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard023
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard024
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard025
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard026
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard027
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard028
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Shard029

/-!
# exact P0 forest branch Branch001
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP0CertificateD972
namespace Branch001

/- Root 0, exact path ((1, 'right'), (0, 'left')), 1146 retained leaves. -/
def tree : RationalTetraSubdivision Rat :=
  (.split (3 : Fin 6)
    (.split (2 : Fin 6)
      (.split (5 : Fin 6)
        (.split (2 : Fin 6)
          Shard015.tree
          Shard016.tree
        )
        (.split (3 : Fin 6)
          Shard017.tree
          Shard018.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          Shard019.tree
          Shard020.tree
        )
        (.split (2 : Fin 6)
          Shard021.tree
          Shard022.tree
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (3 : Fin 6)
        Shard023.tree
        (.split (0 : Fin 6)
          Shard024.tree
          Shard025.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (4 : Fin 6)
          Shard026.tree
          Shard027.tree
        )
        (.split (1 : Fin 6)
          Shard028.tree
          Shard029.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP0LeafValidD970 (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
  have hvalid000 :
      Shard015.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard015.root_eq_path] using Shard015.valid
  have hvalid001 :
      Shard016.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard016.root_eq_path] using Shard016.valid
  have hvalid002 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard017.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard017.root_eq_path] using Shard017.valid
  have hvalid004 :
      Shard018.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard018.root_eq_path] using Shard018.valid
  have hvalid005 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard019.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard019.root_eq_path] using Shard019.valid
  have hvalid008 :
      Shard020.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard020.root_eq_path] using Shard020.valid
  have hvalid009 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard021.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard021.root_eq_path] using Shard021.valid
  have hvalid011 :
      Shard022.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard022.root_eq_path] using Shard022.valid
  have hvalid012 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard023.tree.coverValid sectionSixP0LeafValidD970 ((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard023.root_eq_path] using Shard023.valid
  have hvalid016 :
      Shard024.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard024.root_eq_path] using Shard024.valid
  have hvalid017 :
      Shard025.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard025.root_eq_path] using Shard025.valid
  have hvalid018 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard026.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard026.root_eq_path] using Shard026.valid
  have hvalid021 :
      Shard027.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard027.root_eq_path] using Shard027.valid
  have hvalid022 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :
      Shard028.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard028.root_eq_path] using Shard028.valid
  have hvalid024 :
      Shard029.tree.coverValid sectionSixP0LeafValidD970 (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard029.root_eq_path] using Shard029.valid
  have hvalid025 :=
    valid_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid019 hvalid026
  have hvalid028 :=
    valid_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
      (29070253786467582100033633 / 4915200000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard015.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (921952666996776253860867 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard015.root_eq_path] using Shard015.replay
  have hreplay001 :
      Shard016.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (874930578225101485291267 / 2457600000000000000000000000 : Rat) := by
    simpa only [Shard016.root_eq_path] using Shard016.replay
  have hraw002 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (921952666996776253860867 / 3276800000000000000000000000 : Rat) + (874930578225101485291267 / 2457600000000000000000000000 : Rat) = (6265580313890734702747669 / 9830400000000000000000000000 : Rat))
  have hreplay003 :
      Shard017.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (180704794788565115989739 / 393216000000000000000000000 : Rat) := by
    simpa only [Shard017.root_eq_path] using Shard017.replay
  have hreplay004 :
      Shard018.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ q => q) =
        (343401879570402469323391 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard018.root_eq_path] using Shard018.replay
  have hraw005 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (180704794788565115989739 / 393216000000000000000000000 : Rat) + (343401879570402469323391 / 819200000000000000000000000 : Rat) = (8638442424558957531624167 / 9830400000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (6265580313890734702747669 / 9830400000000000000000000000 : Rat) + (8638442424558957531624167 / 9830400000000000000000000000 : Rat) = (1242001894870807686197653 / 819200000000000000000000000 : Rat))
  have hreplay007 :
      Shard019.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (2362301714443205266039 / 4915200000000000000000000 : Rat) := by
    simpa only [Shard019.root_eq_path] using Shard019.replay
  have hreplay008 :
      Shard020.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (fun _ q => q) =
        (109345069098738062687411 / 245760000000000000000000000 : Rat) := by
    simpa only [Shard020.root_eq_path] using Shard020.replay
  have hraw009 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (2362301714443205266039 / 4915200000000000000000000 : Rat) + (109345069098738062687411 / 245760000000000000000000000 : Rat) = (227460154820898325989361 / 245760000000000000000000000 : Rat))
  have hreplay010 :
      Shard021.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (fun _ q => q) =
        (72583737980168437327619 / 153600000000000000000000000 : Rat) := by
    simpa only [Shard021.root_eq_path] using Shard021.replay
  have hreplay011 :
      Shard022.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (fun _ q => q) =
        (311246836597489344349687 / 614400000000000000000000000 : Rat) := by
    simpa only [Shard022.root_eq_path] using Shard022.replay
  have hraw012 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (72583737980168437327619 / 153600000000000000000000000 : Rat) + (311246836597489344349687 / 614400000000000000000000000 : Rat) = (200527262839387697886721 / 204800000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (227460154820898325989361 / 245760000000000000000000000 : Rat) + (200527262839387697886721 / 204800000000000000000000000 : Rat) = (2340464351140817817267131 / 1228800000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (1242001894870807686197653 / 819200000000000000000000000 : Rat) + (2340464351140817817267131 / 1228800000000000000000000000 : Rat) = (8406934386894058693127221 / 2457600000000000000000000000 : Rat))
  have hreplay015 :
      Shard023.tree.replayWeightRat ((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (fun _ q => q) =
        (571802236296619207863539 / 983040000000000000000000000 : Rat) := by
    simpa only [Shard023.root_eq_path] using Shard023.replay
  have hreplay016 :
      Shard024.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ q => q) =
        (1401346692769992804685543 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard024.root_eq_path] using Shard024.replay
  have hreplay017 :
      Shard025.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ q => q) =
        (203318066733452593913513 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard025.root_eq_path] using Shard025.replay
  have hraw018 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (1401346692769992804685543 / 9830400000000000000000000000 : Rat) + (203318066733452593913513 / 819200000000000000000000000 : Rat) = (3841163493571423931647699 / 9830400000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (571802236296619207863539 / 983040000000000000000000000 : Rat) + (3841163493571423931647699 / 9830400000000000000000000000 : Rat) = (3186395285512538670094363 / 3276800000000000000000000000 : Rat))
  have hreplay020 :
      Shard026.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ q => q) =
        (2756737334246652949433911 / 9830400000000000000000000000 : Rat) := by
    simpa only [Shard026.root_eq_path] using Shard026.replay
  have hreplay021 :
      Shard027.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ q => q) =
        (593095918792361984327563 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard027.root_eq_path] using Shard027.replay
  have hraw022 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (2756737334246652949433911 / 9830400000000000000000000000 : Rat) + (593095918792361984327563 / 1638400000000000000000000000 : Rat) = (6315312847000824855399289 / 9830400000000000000000000000 : Rat))
  have hreplay023 :
      Shard028.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ q => q) =
        (2072221320385334198720567 / 4915200000000000000000000000 : Rat) := by
    simpa only [Shard028.root_eq_path] using Shard028.replay
  have hreplay024 :
      Shard029.tree.replayWeightRat (((((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ q => q) =
        (449382868104982016443487 / 983040000000000000000000000 : Rat) := by
    simpa only [Shard029.root_eq_path] using Shard029.replay
  have hraw025 :=
    replay_split (T := (((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (2072221320385334198720567 / 4915200000000000000000000000 : Rat) + (449382868104982016443487 / 983040000000000000000000000 : Rat) = (719855943485040713489667 / 819200000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (2 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (6315312847000824855399289 / 9830400000000000000000000000 : Rat) + (719855943485040713489667 / 819200000000000000000000000 : Rat) = (14953584168821313417275293 / 9830400000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay019 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (3186395285512538670094363 / 3276800000000000000000000000 : Rat) + (14953584168821313417275293 / 9830400000000000000000000000 : Rat) = (12256385012679464713779191 / 4915200000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((sectionSixP0RootD971 (0 : Fin 3)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (8406934386894058693127221 / 2457600000000000000000000000 : Rat) + (12256385012679464713779191 / 4915200000000000000000000000 : Rat) = (29070253786467582100033633 / 4915200000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch001
end SectionSixP0CertificateD972
end PrimesRestrictedDigits
