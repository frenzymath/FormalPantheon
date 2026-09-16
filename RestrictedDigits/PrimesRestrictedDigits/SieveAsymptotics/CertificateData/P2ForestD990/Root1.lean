import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch007
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch008
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch009
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch011
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch012
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch013
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch016
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch017
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch018
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch019

/-!
# exact P2 forest root Root1
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Root1

/- Root 1, exact path (), 4726 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Branch006.tree
          Branch007.tree
        )
        (.split (2 : Fin 6)
          Branch008.tree
          Branch009.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          Branch010.tree
          Branch011.tree
        )
        (.split (3 : Fin 6)
          Branch012.tree
          Branch013.tree
        )
      )
    )
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        Branch016.tree
        Branch017.tree
      )
      (.split (1 : Fin 6)
        Branch018.tree
        Branch019.tree
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (sectionSixP2RootD974 (1 : Fin 3)) = true := by
  have hvalid000 :
      Branch006.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    exact Branch006.valid
  have hvalid001 :
      Branch007.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    exact Branch007.valid
  have hvalid002 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Branch008.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    exact Branch008.valid
  have hvalid004 :
      Branch009.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    exact Branch009.valid
  have hvalid005 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Branch010.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    exact Branch010.valid
  have hvalid008 :
      Branch011.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    exact Branch011.valid
  have hvalid009 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Branch012.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    exact Branch012.valid
  have hvalid011 :
      Branch013.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    exact Branch013.valid
  have hvalid012 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Branch016.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    exact Branch016.valid
  have hvalid016 :
      Branch017.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    exact Branch017.valid
  have hvalid017 :=
    valid_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Branch018.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    exact Branch018.valid
  have hvalid019 :
      Branch019.tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    exact Branch019.valid
  have hvalid020 :=
    valid_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := (sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :=
    valid_split (T := sectionSixP2RootD974 (1 : Fin 3)) (e := (1 : Fin 6)) hvalid014 hvalid021
  simpa only [tree] using hvalid022

theorem replay :
    tree.replayWeightRat (sectionSixP2RootD974 (1 : Fin 3)) (fun _ p => p.upper) =
      (99600047880749804633259087 / 32768000000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch006.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (3744149676998589864216513 / 16384000000000000000000000000 : Rat) := by
    exact Branch006.replay
  have hreplay001 :
      Branch007.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (169861201307451064707723 / 819200000000000000000000000 : Rat) := by
    exact Branch007.replay
  have hraw002 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (3744149676998589864216513 / 16384000000000000000000000000 : Rat) + (169861201307451064707723 / 819200000000000000000000000 : Rat) = (7141373703147611158370973 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Branch008.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (2605771117477186669109277 / 16384000000000000000000000000 : Rat) := by
    exact Branch008.replay
  have hreplay004 :
      Branch009.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1161644492720905982634699 / 4096000000000000000000000000 : Rat) := by
    exact Branch009.replay
  have hraw005 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (2605771117477186669109277 / 16384000000000000000000000000 : Rat) + (1161644492720905982634699 / 4096000000000000000000000000 : Rat) = (7252349088360810599648073 / 16384000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (7141373703147611158370973 / 16384000000000000000000000000 : Rat) + (7252349088360810599648073 / 16384000000000000000000000000 : Rat) = (7196861395754210879009523 / 8192000000000000000000000000 : Rat))
  have hreplay007 :
      Branch010.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1482554046486268268241489 / 16384000000000000000000000000 : Rat) := by
    exact Branch010.replay
  have hreplay008 :
      Branch011.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (3385000583974365643363869 / 16384000000000000000000000000 : Rat) := by
    exact Branch011.replay
  have hraw009 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (1482554046486268268241489 / 16384000000000000000000000000 : Rat) + (3385000583974365643363869 / 16384000000000000000000000000 : Rat) = (2433777315230316955802679 / 8192000000000000000000000000 : Rat))
  have hreplay010 :
      Branch012.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (2290016586224228059037907 / 8192000000000000000000000000 : Rat) := by
    exact Branch012.replay
  have hreplay011 :
      Branch013.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (7853390487429774676711749 / 32768000000000000000000000000 : Rat) := by
    exact Branch013.replay
  have hraw012 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (2290016586224228059037907 / 8192000000000000000000000000 : Rat) + (7853390487429774676711749 / 32768000000000000000000000000 : Rat) = (17013456832326686912863377 / 32768000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (2433777315230316955802679 / 8192000000000000000000000000 : Rat) + (17013456832326686912863377 / 32768000000000000000000000000 : Rat) = (26748566093247954736074093 / 32768000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (sectionSixP2RootD974 (1 : Fin 3)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (7196861395754210879009523 / 8192000000000000000000000000 : Rat) + (26748566093247954736074093 / 32768000000000000000000000000 : Rat) = (11107202335252959650422437 / 6553600000000000000000000000 : Rat))
  have hreplay015 :
      Branch016.tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (269455778614379576055087 / 1638400000000000000000000000 : Rat) := by
    exact Branch016.replay
  have hreplay016 :
      Branch017.tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (4594703345088479150601573 / 16384000000000000000000000000 : Rat) := by
    exact Branch017.replay
  have hraw017 :=
    replay_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (269455778614379576055087 / 1638400000000000000000000000 : Rat) + (4594703345088479150601573 / 16384000000000000000000000000 : Rat) = (7289261131232274911152443 / 16384000000000000000000000000 : Rat))
  have hreplay018 :
      Branch018.tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4639071488530620019576509 / 8192000000000000000000000000 : Rat) := by
    exact Branch018.replay
  have hreplay019 :
      Branch019.tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (546461399394898824026799 / 1638400000000000000000000000 : Rat) := by
    exact Branch019.replay
  have hraw020 :=
    replay_split (T := ((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (4639071488530620019576509 / 8192000000000000000000000000 : Rat) + (546461399394898824026799 / 1638400000000000000000000000 : Rat) = (921422310688139267463813 / 1024000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := (sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (7289261131232274911152443 / 16384000000000000000000000000 : Rat) + (921422310688139267463813 / 1024000000000000000000000000 : Rat) = (22032018102242503190573451 / 16384000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := sectionSixP2RootD974 (1 : Fin 3)) (e := (1 : Fin 6)) hreplay014 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (11107202335252959650422437 / 6553600000000000000000000000 : Rat) + (22032018102242503190573451 / 16384000000000000000000000000 : Rat) = (99600047880749804633259087 / 32768000000000000000000000000 : Rat))
  simpa only [tree] using hreplay022

end Root1
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
