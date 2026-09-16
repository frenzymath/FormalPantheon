import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard529
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard530
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard531
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard532
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard533
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard534
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard535
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard536
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard537
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard538
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard539
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard540
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard541
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard542
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard543

/-!
# exact P2 forest branch Branch032
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch032

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'left'), (1, 'left'), (3, 'left')), 284 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          Shard529.tree
          Shard530.tree
        )
        (.split (4 : Fin 6)
          Shard531.tree
          Shard532.tree
        )
      )
      (.split (1 : Fin 6)
        Shard533.tree
        (.split (4 : Fin 6)
          Shard534.tree
          Shard535.tree
        )
      )
    )
    (.split (1 : Fin 6)
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard536.tree
          Shard537.tree
        )
        (.split (3 : Fin 6)
          Shard538.tree
          Shard539.tree
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Shard540.tree
          Shard541.tree
        )
        (.split (2 : Fin 6)
          Shard542.tree
          Shard543.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard529.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard529.root_eq_path] using Shard529.valid
  have hvalid001 :
      Shard530.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard530.root_eq_path] using Shard530.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard531.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard531.root_eq_path] using Shard531.valid
  have hvalid004 :
      Shard532.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard532.root_eq_path] using Shard532.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard533.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard533.root_eq_path] using Shard533.valid
  have hvalid008 :
      Shard534.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard534.root_eq_path] using Shard534.valid
  have hvalid009 :
      Shard535.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard535.root_eq_path] using Shard535.valid
  have hvalid010 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard536.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard536.root_eq_path] using Shard536.valid
  have hvalid014 :
      Shard537.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard537.root_eq_path] using Shard537.valid
  have hvalid015 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard538.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard538.root_eq_path] using Shard538.valid
  have hvalid017 :
      Shard539.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard539.root_eq_path] using Shard539.valid
  have hvalid018 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard540.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard540.root_eq_path] using Shard540.valid
  have hvalid021 :
      Shard541.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard541.root_eq_path] using Shard541.valid
  have hvalid022 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid020 hvalid021
  have hvalid023 :
      Shard542.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard542.root_eq_path] using Shard542.valid
  have hvalid024 :
      Shard543.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard543.root_eq_path] using Shard543.valid
  have hvalid025 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid019 hvalid026
  have hvalid028 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid012 hvalid027
  simpa only [tree] using hvalid028

theorem replay :
    tree.replayWeightRat ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
      (4094054545944017351419209 / 3276800000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard529.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (714806601894018438724809 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard529.root_eq_path] using Shard529.replay
  have hreplay001 :
      Shard530.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (517666545914261861570409 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard530.root_eq_path] using Shard530.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (714806601894018438724809 / 16384000000000000000000000000 : Rat) + (517666545914261861570409 / 8192000000000000000000000000 : Rat) = (1750139693722542161865627 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard531.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (34207627317533173244457 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard531.root_eq_path] using Shard531.replay
  have hreplay004 :
      Shard532.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (126312998475068572316337 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard532.root_eq_path] using Shard532.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (34207627317533173244457 / 512000000000000000000000000 : Rat) + (126312998475068572316337 / 1638400000000000000000000000 : Rat) = (1178887029455873633492997 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (1750139693722542161865627 / 16384000000000000000000000000 : Rat) + (1178887029455873633492997 / 8192000000000000000000000000 : Rat) = (4107913752634289428851621 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Shard533.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (273423176460982499420763 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard533.root_eq_path] using Shard533.replay
  have hreplay008 :
      Shard534.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2916967210278001337043 / 40960000000000000000000000 : Rat) := by
    simpa only [Shard534.root_eq_path] using Shard534.replay
  have hreplay009 :
      Shard535.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (353892716716976034847173 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard535.root_eq_path] using Shard535.replay
  have hraw010 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (2916967210278001337043 / 40960000000000000000000000 : Rat) + (353892716716976034847173 / 4096000000000000000000000000 : Rat) = (645589437744776168551473 / 4096000000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (273423176460982499420763 / 2048000000000000000000000000 : Rat) + (645589437744776168551473 / 4096000000000000000000000000 : Rat) = (1192435790666741167392999 / 4096000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (4107913752634289428851621 / 16384000000000000000000000000 : Rat) + (1192435790666741167392999 / 4096000000000000000000000000 : Rat) = (8877656915301254098423617 / 16384000000000000000000000000 : Rat))
  have hreplay013 :
      Shard536.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (66998877359524426483461 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard536.root_eq_path] using Shard536.replay
  have hreplay014 :
      Shard537.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (23590554167987942909013 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard537.root_eq_path] using Shard537.replay
  have hraw015 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (66998877359524426483461 / 819200000000000000000000000 : Rat) + (23590554167987942909013 / 256000000000000000000000000 : Rat) = (712443253485429218961513 / 4096000000000000000000000000 : Rat))
  have hreplay016 :
      Shard538.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (711267983838654720452163 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard538.root_eq_path] using Shard538.replay
  have hreplay017 :
      Shard539.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (711032989842090406335087 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard539.root_eq_path] using Shard539.replay
  have hraw018 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (711267983838654720452163 / 8192000000000000000000000000 : Rat) + (711032989842090406335087 / 8192000000000000000000000000 : Rat) = (5689203894722980507149 / 32768000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (712443253485429218961513 / 4096000000000000000000000000 : Rat) + (5689203894722980507149 / 32768000000000000000000000 : Rat) = (711796870162900891177569 / 2048000000000000000000000000 : Rat))
  have hreplay020 :
      Shard540.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (92303245791501993809793 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard540.root_eq_path] using Shard540.replay
  have hreplay021 :
      Shard541.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (45208613646453818628963 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard541.root_eq_path] using Shard541.replay
  have hraw022 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay020 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (92303245791501993809793 / 1024000000000000000000000000 : Rat) + (45208613646453818628963 / 512000000000000000000000000 : Rat) = (182720473084409631067719 / 1024000000000000000000000000 : Rat))
  have hreplay023 :
      Shard542.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (684533178941099385765789 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard542.root_eq_path] using Shard542.replay
  have hreplay024 :
      Shard543.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (802823462941436330318397 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard543.root_eq_path] using Shard543.replay
  have hraw025 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (684533178941099385765789 / 8192000000000000000000000000 : Rat) + (802823462941436330318397 / 8192000000000000000000000000 : Rat) = (743678320941267858042093 / 4096000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (182720473084409631067719 / 1024000000000000000000000000 : Rat) + (743678320941267858042093 / 4096000000000000000000000000 : Rat) = (1474560213278906382312969 / 4096000000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay019 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (711796870162900891177569 / 2048000000000000000000000000 : Rat) + (1474560213278906382312969 / 4096000000000000000000000000 : Rat) = (2898153953604708164668107 / 4096000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay012 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (8877656915301254098423617 / 16384000000000000000000000000 : Rat) + (2898153953604708164668107 / 4096000000000000000000000000 : Rat) = (4094054545944017351419209 / 3276800000000000000000000000 : Rat))
  simpa only [tree] using hreplay028

end Branch032
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
