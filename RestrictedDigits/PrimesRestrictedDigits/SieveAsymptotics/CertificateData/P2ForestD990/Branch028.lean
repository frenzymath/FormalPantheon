import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard444
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard445
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard446
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard447
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard448
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard449
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard450
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard451
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard452
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard453
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard454
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard455
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard456
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard457
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard458
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard459
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard460
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard461
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard462
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard463
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard464

/-!
# exact P2 forest branch Branch028
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch028

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'left')), 520 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (1 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          (.split (5 : Fin 6)
            Shard444.tree
            Shard445.tree
          )
          Shard446.tree
        )
        (.split (5 : Fin 6)
          Shard447.tree
          Shard448.tree
        )
      )
      (.split (3 : Fin 6)
        (.split (1 : Fin 6)
          Shard449.tree
          Shard450.tree
        )
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            Shard451.tree
            Shard452.tree
          )
          Shard453.tree
        )
      )
    )
    (.split (4 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          (.split (1 : Fin 6)
            Shard454.tree
            Shard455.tree
          )
          (.split (0 : Fin 6)
            Shard456.tree
            Shard457.tree
          )
        )
        (.split (1 : Fin 6)
          Shard458.tree
          (.split (0 : Fin 6)
            Shard459.tree
            Shard460.tree
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (1 : Fin 6)
          Shard461.tree
          Shard462.tree
        )
        (.split (0 : Fin 6)
          Shard463.tree
          Shard464.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard444.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard444.root_eq_path] using Shard444.valid
  have hvalid001 :
      Shard445.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard445.root_eq_path] using Shard445.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard446.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard446.root_eq_path] using Shard446.valid
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid002 hvalid003
  have hvalid005 :
      Shard447.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard447.root_eq_path] using Shard447.valid
  have hvalid006 :
      Shard448.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard448.root_eq_path] using Shard448.valid
  have hvalid007 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid004 hvalid007
  have hvalid009 :
      Shard449.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard449.root_eq_path] using Shard449.valid
  have hvalid010 :
      Shard450.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard450.root_eq_path] using Shard450.valid
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid009 hvalid010
  have hvalid012 :
      Shard451.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard451.root_eq_path] using Shard451.valid
  have hvalid013 :
      Shard452.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard452.root_eq_path] using Shard452.valid
  have hvalid014 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid012 hvalid013
  have hvalid015 :
      Shard453.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard453.root_eq_path] using Shard453.valid
  have hvalid016 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid014 hvalid015
  have hvalid017 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid011 hvalid016
  have hvalid018 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid008 hvalid017
  have hvalid019 :
      Shard454.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard454.root_eq_path] using Shard454.valid
  have hvalid020 :
      Shard455.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard455.root_eq_path] using Shard455.valid
  have hvalid021 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid019 hvalid020
  have hvalid022 :
      Shard456.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard456.root_eq_path] using Shard456.valid
  have hvalid023 :
      Shard457.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard457.root_eq_path] using Shard457.valid
  have hvalid024 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid023
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid021 hvalid024
  have hvalid026 :
      Shard458.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard458.root_eq_path] using Shard458.valid
  have hvalid027 :
      Shard459.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard459.root_eq_path] using Shard459.valid
  have hvalid028 :
      Shard460.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard460.root_eq_path] using Shard460.valid
  have hvalid029 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid027 hvalid028
  have hvalid030 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid026 hvalid029
  have hvalid031 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid025 hvalid030
  have hvalid032 :
      Shard461.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard461.root_eq_path] using Shard461.valid
  have hvalid033 :
      Shard462.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard462.root_eq_path] using Shard462.valid
  have hvalid034 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid032 hvalid033
  have hvalid035 :
      Shard463.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard463.root_eq_path] using Shard463.valid
  have hvalid036 :
      Shard464.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard464.root_eq_path] using Shard464.valid
  have hvalid037 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid035 hvalid036
  have hvalid038 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid034 hvalid037
  have hvalid039 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid031 hvalid038
  have hvalid040 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid018 hvalid039
  simpa only [tree] using hvalid040

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
      (879763381511492521311777 / 512000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard444.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (135775063761642257003163 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard444.root_eq_path] using Shard444.replay
  have hreplay001 :
      Shard445.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (683228489346193969404189 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard445.root_eq_path] using Shard445.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (135775063761642257003163 / 4096000000000000000000000000 : Rat) + (683228489346193969404189 / 16384000000000000000000000000 : Rat) = (1226328744392762997416841 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard446.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (97702247425710154693779 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard446.root_eq_path] using Shard446.replay
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay002 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (1226328744392762997416841 / 16384000000000000000000000000 : Rat) + (97702247425710154693779 / 1024000000000000000000000000 : Rat) = (557912940640825094503461 / 3276800000000000000000000000 : Rat))
  have hreplay005 :
      Shard447.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (994457185235030756643363 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard447.root_eq_path] using Shard447.replay
  have hreplay006 :
      Shard448.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (502632605221843034891493 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard448.root_eq_path] using Shard448.replay
  have hraw007 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (994457185235030756643363 / 8192000000000000000000000000 : Rat) + (502632605221843034891493 / 4096000000000000000000000000 : Rat) = (1999722395678716826426349 / 8192000000000000000000000000 : Rat))
  have hraw008 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay004 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (557912940640825094503461 / 3276800000000000000000000000 : Rat) + (1999722395678716826426349 / 8192000000000000000000000000 : Rat) = (6789009494561559125370003 / 16384000000000000000000000000 : Rat))
  have hreplay009 :
      Shard449.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1276579060891120460259603 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard449.root_eq_path] using Shard449.replay
  have hreplay010 :
      Shard450.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (1123666557443458020169479 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard450.root_eq_path] using Shard450.replay
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay009 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (1276579060891120460259603 / 8192000000000000000000000000 : Rat) + (1123666557443458020169479 / 8192000000000000000000000000 : Rat) = (1200122809167289240214541 / 4096000000000000000000000000 : Rat))
  have hreplay012 :
      Shard451.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (63501587651378870176653 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard451.root_eq_path] using Shard451.replay
  have hreplay013 :
      Shard452.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (558865098435579811206183 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard452.root_eq_path] using Shard452.replay
  have hraw014 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay012 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (63501587651378870176653 / 819200000000000000000000000 : Rat) + (558865098435579811206183 / 8192000000000000000000000000 : Rat) = (1193880974949368512972713 / 8192000000000000000000000000 : Rat))
  have hreplay015 :
      Shard453.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (594953889770679659054199 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard453.root_eq_path] using Shard453.replay
  have hraw016 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay014 hreplay015
  have hreplay016 := hraw016.trans
    (by norm_num : (1193880974949368512972713 / 8192000000000000000000000000 : Rat) + (594953889770679659054199 / 4096000000000000000000000000 : Rat) = (2383788754490727831081111 / 8192000000000000000000000000 : Rat))
  have hraw017 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay011 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (1200122809167289240214541 / 4096000000000000000000000000 : Rat) + (2383788754490727831081111 / 8192000000000000000000000000 : Rat) = (4784034372825306311510193 / 8192000000000000000000000000 : Rat))
  have hraw018 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay008 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (6789009494561559125370003 / 16384000000000000000000000000 : Rat) + (4784034372825306311510193 / 8192000000000000000000000000 : Rat) = (16357078240212171748390389 / 16384000000000000000000000000 : Rat))
  have hreplay019 :
      Shard454.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (93868412220452661666831 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard454.root_eq_path] using Shard454.replay
  have hreplay020 :
      Shard455.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (420975965381316760969461 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard455.root_eq_path] using Shard455.replay
  have hraw021 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay019 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (93868412220452661666831 / 3276800000000000000000000000 : Rat) + (420975965381316760969461 / 16384000000000000000000000000 : Rat) = (13911219163805938582869 / 256000000000000000000000000 : Rat))
  have hreplay022 :
      Shard456.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (152572026502006614805509 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard456.root_eq_path] using Shard456.replay
  have hreplay023 :
      Shard457.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (259711989511604236628391 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard457.root_eq_path] using Shard457.replay
  have hraw024 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay023
  have hreplay024 := hraw024.trans
    (by norm_num : (152572026502006614805509 / 4096000000000000000000000000 : Rat) + (259711989511604236628391 / 8192000000000000000000000000 : Rat) = (564856042515617466239409 / 8192000000000000000000000000 : Rat))
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay021 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (13911219163805938582869 / 256000000000000000000000000 : Rat) + (564856042515617466239409 / 8192000000000000000000000000 : Rat) = (1010015055757407500891217 / 8192000000000000000000000000 : Rat))
  have hreplay026 :
      Shard458.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (297044062509272156206011 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard458.root_eq_path] using Shard458.replay
  have hreplay027 :
      Shard459.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (325910919124460349054351 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard459.root_eq_path] using Shard459.replay
  have hreplay028 :
      Shard460.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (280818579404803214076093 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard460.root_eq_path] using Shard460.replay
  have hraw029 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay027 hreplay028
  have hreplay029 := hraw029.trans
    (by norm_num : (325910919124460349054351 / 8192000000000000000000000000 : Rat) + (280818579404803214076093 / 8192000000000000000000000000 : Rat) = (151682374632315890782611 / 2048000000000000000000000000 : Rat))
  have hraw030 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay026 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (297044062509272156206011 / 3276800000000000000000000000 : Rat) + (151682374632315890782611 / 2048000000000000000000000000 : Rat) = (2698679309604887907290943 / 16384000000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay025 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (1010015055757407500891217 / 8192000000000000000000000000 : Rat) + (2698679309604887907290943 / 16384000000000000000000000000 : Rat) = (4718709421119702909073377 / 16384000000000000000000000000 : Rat))
  have hreplay032 :
      Shard461.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (498722814993290742948933 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard461.root_eq_path] using Shard461.replay
  have hreplay033 :
      Shard462.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (460872703131423891393591 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard462.root_eq_path] using Shard462.replay
  have hraw034 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay032 hreplay033
  have hreplay034 := hraw034.trans
    (by norm_num : (498722814993290742948933 / 4096000000000000000000000000 : Rat) + (460872703131423891393591 / 4096000000000000000000000000 : Rat) = (239898879531178658585631 / 1024000000000000000000000000 : Rat))
  have hreplay035 :
      Shard463.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (37747806400812882261969 / 327680000000000000000000000 : Rat) := by
    simpa only [Shard463.root_eq_path] using Shard463.replay
  have hreplay036 :
      Shard464.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (168858519312047921755569 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard464.root_eq_path] using Shard464.replay
  have hraw037 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay035 hreplay036
  have hreplay037 := hraw037.trans
    (by norm_num : (37747806400812882261969 / 327680000000000000000000000 : Rat) + (168858519312047921755569 / 2048000000000000000000000000 : Rat) = (1619129237268513743571501 / 8192000000000000000000000000 : Rat))
  have hraw038 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay034 hreplay037
  have hreplay038 := hraw038.trans
    (by norm_num : (239898879531178658585631 / 1024000000000000000000000000 : Rat) + (1619129237268513743571501 / 8192000000000000000000000000 : Rat) = (3538320273517943012256549 / 8192000000000000000000000000 : Rat))
  have hraw039 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay031 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (4718709421119702909073377 / 16384000000000000000000000000 : Rat) + (3538320273517943012256549 / 8192000000000000000000000000 : Rat) = (471813998726223557343459 / 655360000000000000000000000 : Rat))
  have hraw040 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay018 hreplay039
  have hreplay040 := hraw040.trans
    (by norm_num : (16357078240212171748390389 / 16384000000000000000000000000 : Rat) + (471813998726223557343459 / 655360000000000000000000000 : Rat) = (879763381511492521311777 / 512000000000000000000000000 : Rat))
  simpa only [tree] using hreplay040

end Branch028
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
