import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard255
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard256
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard257
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard258
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard259
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard260
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard261
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard262
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard263
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard264
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard265
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard266
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard267
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard268
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard269
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard270
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard271
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard272

/-!
# exact P2 forest branch Branch015
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch015

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left'), (5, 'right')), 401 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard255.tree
          Shard256.tree
        )
        (.split (4 : Fin 6)
          Shard257.tree
          Shard258.tree
        )
      )
      (.split (1 : Fin 6)
        Shard259.tree
        (.split (2 : Fin 6)
          Shard260.tree
          Shard261.tree
        )
      )
    )
    (.split (5 : Fin 6)
      (.split (2 : Fin 6)
        (.split (5 : Fin 6)
          Shard262.tree
          Shard263.tree
        )
        (.split (1 : Fin 6)
          Shard264.tree
          Shard265.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (5 : Fin 6)
          Shard266.tree
          (.split (2 : Fin 6)
            Shard267.tree
            Shard268.tree
          )
        )
        (.split (2 : Fin 6)
          (.split (4 : Fin 6)
            Shard269.tree
            Shard270.tree
          )
          (.split (0 : Fin 6)
            Shard271.tree
            Shard272.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
  have hvalid000 :
      Shard255.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard255.root_eq_path] using Shard255.valid
  have hvalid001 :
      Shard256.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard256.root_eq_path] using Shard256.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard257.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard257.root_eq_path] using Shard257.valid
  have hvalid004 :
      Shard258.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard258.root_eq_path] using Shard258.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard259.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard259.root_eq_path] using Shard259.valid
  have hvalid008 :
      Shard260.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard260.root_eq_path] using Shard260.valid
  have hvalid009 :
      Shard261.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard261.root_eq_path] using Shard261.valid
  have hvalid010 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard262.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard262.root_eq_path] using Shard262.valid
  have hvalid014 :
      Shard263.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard263.root_eq_path] using Shard263.valid
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard264.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard264.root_eq_path] using Shard264.valid
  have hvalid017 :
      Shard265.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard265.root_eq_path] using Shard265.valid
  have hvalid018 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :
      Shard266.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard266.root_eq_path] using Shard266.valid
  have hvalid021 :
      Shard267.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard267.root_eq_path] using Shard267.valid
  have hvalid022 :
      Shard268.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard268.root_eq_path] using Shard268.valid
  have hvalid023 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid020 hvalid023
  have hvalid025 :
      Shard269.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard269.root_eq_path] using Shard269.valid
  have hvalid026 :
      Shard270.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard270.root_eq_path] using Shard270.valid
  have hvalid027 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :
      Shard271.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard271.root_eq_path] using Shard271.valid
  have hvalid029 :
      Shard272.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard272.root_eq_path] using Shard272.valid
  have hvalid030 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hvalid027 hvalid030
  have hvalid032 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid024 hvalid031
  have hvalid033 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid019 hvalid032
  have hvalid034 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid012 hvalid033
  simpa only [tree] using hvalid034

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
      (2180714839918563159149013 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard255.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (51837303246924412161117 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard255.root_eq_path] using Shard255.replay
  have hreplay001 :
      Shard256.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (3343416629501189435481 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard256.root_eq_path] using Shard256.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (51837303246924412161117 / 8192000000000000000000000000 : Rat) + (3343416629501189435481 / 409600000000000000000000000 : Rat) = (118705635836948200870737 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard257.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (51847057782916163597853 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard257.root_eq_path] using Shard257.replay
  have hreplay004 :
      Shard258.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (22575023010582580504971 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard258.root_eq_path] using Shard258.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (51847057782916163597853 / 8192000000000000000000000000 : Rat) + (22575023010582580504971 / 4096000000000000000000000000 : Rat) = (19399420760816264921559 / 1638400000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (118705635836948200870737 / 8192000000000000000000000000 : Rat) + (19399420760816264921559 / 1638400000000000000000000000 : Rat) = (53925684910257381369633 / 2048000000000000000000000000 : Rat))
  have hreplay007 :
      Shard259.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (28929237009450919543773 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard259.root_eq_path] using Shard259.replay
  have hreplay008 :
      Shard260.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (34166355979860818449281 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard260.root_eq_path] using Shard260.replay
  have hreplay009 :
      Shard261.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (51219679851223232570739 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard261.root_eq_path] using Shard261.replay
  have hraw010 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (34166355979860818449281 / 8192000000000000000000000000 : Rat) + (51219679851223232570739 / 16384000000000000000000000000 : Rat) = (119552391810944869469301 / 16384000000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (28929237009450919543773 / 2048000000000000000000000000 : Rat) + (119552391810944869469301 / 16384000000000000000000000000 : Rat) = (70197257577310445163897 / 3276800000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (53925684910257381369633 / 2048000000000000000000000000 : Rat) + (70197257577310445163897 / 3276800000000000000000000000 : Rat) = (782391767168611276776549 / 16384000000000000000000000000 : Rat))
  have hreplay013 :
      Shard262.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (84299349261006193447683 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard262.root_eq_path] using Shard262.replay
  have hreplay014 :
      Shard263.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (94708554038076252619197 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard263.root_eq_path] using Shard263.replay
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (84299349261006193447683 / 8192000000000000000000000000 : Rat) + (94708554038076252619197 / 8192000000000000000000000000 : Rat) = (559399697809632643959 / 25600000000000000000000000 : Rat))
  have hreplay016 :
      Shard264.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (32848139929527135920061 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard264.root_eq_path] using Shard264.replay
  have hreplay017 :
      Shard265.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (85344023153441625843537 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard265.root_eq_path] using Shard265.replay
  have hraw018 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (32848139929527135920061 / 3276800000000000000000000000 : Rat) + (85344023153441625843537 / 16384000000000000000000000000 : Rat) = (124792361400538652721921 / 8192000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (559399697809632643959 / 25600000000000000000000000 : Rat) + (124792361400538652721921 / 8192000000000000000000000000 : Rat) = (303800264699621098788801 / 8192000000000000000000000000 : Rat))
  have hreplay020 :
      Shard266.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (241079571266645485293201 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard266.root_eq_path] using Shard266.replay
  have hreplay021 :
      Shard267.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (158644791676796902078761 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard267.root_eq_path] using Shard267.replay
  have hreplay022 :
      Shard268.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (55600343019949693360437 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard268.root_eq_path] using Shard268.replay
  have hraw023 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (158644791676796902078761 / 16384000000000000000000000000 : Rat) + (55600343019949693360437 / 8192000000000000000000000000 : Rat) = (53969095543339257759927 / 3276800000000000000000000000 : Rat))
  have hraw024 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay020 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (241079571266645485293201 / 16384000000000000000000000000 : Rat) + (53969095543339257759927 / 3276800000000000000000000000 : Rat) = (127731262245835443523209 / 4096000000000000000000000000 : Rat))
  have hreplay025 :
      Shard269.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (2786308124546894618097 / 409600000000000000000000000 : Rat) := by
    simpa only [Shard269.root_eq_path] using Shard269.replay
  have hreplay026 :
      Shard270.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (13750450074638643894939 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard270.root_eq_path] using Shard270.replay
  have hraw027 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (2786308124546894618097 / 409600000000000000000000000 : Rat) + (13750450074638643894939 / 3276800000000000000000000000 : Rat) = (7208183014202760167943 / 655360000000000000000000000 : Rat))
  have hreplay028 :
      Shard271.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (24293918074829371828713 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard271.root_eq_path] using Shard271.replay
  have hreplay029 :
      Shard272.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (2040203314505606513841 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard272.root_eq_path] using Shard272.replay
  have hraw030 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (24293918074829371828713 / 8192000000000000000000000000 : Rat) + (2040203314505606513841 / 655360000000000000000000000 : Rat) = (99592919012298906503451 / 16384000000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (2 : Fin 6)) hreplay027 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (7208183014202760167943 / 655360000000000000000000000 : Rat) + (99592919012298906503451 / 16384000000000000000000000000 : Rat) = (139898747183683955351013 / 8192000000000000000000000000 : Rat))
  have hraw032 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay024 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (127731262245835443523209 / 4096000000000000000000000000 : Rat) + (139898747183683955351013 / 8192000000000000000000000000 : Rat) = (395361271675354842397431 / 8192000000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay019 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (303800264699621098788801 / 8192000000000000000000000000 : Rat) + (395361271675354842397431 / 8192000000000000000000000000 : Rat) = (87395192046871992648279 / 1024000000000000000000000000 : Rat))
  have hraw034 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay012 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (782391767168611276776549 / 16384000000000000000000000000 : Rat) + (87395192046871992648279 / 1024000000000000000000000000 : Rat) = (2180714839918563159149013 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay034

end Branch015
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
