import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard489
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard490
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard491
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard492
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard493
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard494
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard495
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard496
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard497
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard498
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard499
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard500
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard501
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard502
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard503
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard504
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard505
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard506
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard507
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard508
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard509
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard510
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard511

/-!
# exact P2 forest branch Branch030
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch030

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'right'), (4, 'left')), 494 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (5 : Fin 6)
        (.split (4 : Fin 6)
          Shard489.tree
          Shard490.tree
        )
        (.split (4 : Fin 6)
          (.split (1 : Fin 6)
            Shard491.tree
            Shard492.tree
          )
          (.split (1 : Fin 6)
            Shard493.tree
            Shard494.tree
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          Shard495.tree
          (.split (1 : Fin 6)
            Shard496.tree
            Shard497.tree
          )
        )
        (.split (1 : Fin 6)
          Shard498.tree
          (.split (0 : Fin 6)
            Shard499.tree
            Shard500.tree
          )
        )
      )
    )
    (.split (0 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.split (2 : Fin 6)
            Shard501.tree
            Shard502.tree
          )
          Shard503.tree
        )
        (.split (3 : Fin 6)
          (.split (3 : Fin 6)
            Shard504.tree
            Shard505.tree
          )
          Shard506.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (1 : Fin 6)
          Shard507.tree
          Shard508.tree
        )
        (.split (1 : Fin 6)
          (.split (1 : Fin 6)
            Shard509.tree
            Shard510.tree
          )
          Shard511.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard489.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard489.root_eq_path] using Shard489.valid
  have hvalid001 :
      Shard490.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard490.root_eq_path] using Shard490.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard491.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard491.root_eq_path] using Shard491.valid
  have hvalid004 :
      Shard492.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard492.root_eq_path] using Shard492.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :
      Shard493.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard493.root_eq_path] using Shard493.valid
  have hvalid007 :
      Shard494.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard494.root_eq_path] using Shard494.valid
  have hvalid008 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid006 hvalid007
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid005 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid009
  have hvalid011 :
      Shard495.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard495.root_eq_path] using Shard495.valid
  have hvalid012 :
      Shard496.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard496.root_eq_path] using Shard496.valid
  have hvalid013 :
      Shard497.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard497.root_eq_path] using Shard497.valid
  have hvalid014 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid012 hvalid013
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid011 hvalid014
  have hvalid016 :
      Shard498.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard498.root_eq_path] using Shard498.valid
  have hvalid017 :
      Shard499.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard499.root_eq_path] using Shard499.valid
  have hvalid018 :
      Shard500.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard500.root_eq_path] using Shard500.valid
  have hvalid019 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid017 hvalid018
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid016 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid015 hvalid020
  have hvalid022 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid010 hvalid021
  have hvalid023 :
      Shard501.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard501.root_eq_path] using Shard501.valid
  have hvalid024 :
      Shard502.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard502.root_eq_path] using Shard502.valid
  have hvalid025 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :
      Shard503.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard503.root_eq_path] using Shard503.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :
      Shard504.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard504.root_eq_path] using Shard504.valid
  have hvalid029 :
      Shard505.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard505.root_eq_path] using Shard505.valid
  have hvalid030 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :
      Shard506.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard506.root_eq_path] using Shard506.valid
  have hvalid032 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid030 hvalid031
  have hvalid033 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hvalid027 hvalid032
  have hvalid034 :
      Shard507.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard507.root_eq_path] using Shard507.valid
  have hvalid035 :
      Shard508.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard508.root_eq_path] using Shard508.valid
  have hvalid036 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid034 hvalid035
  have hvalid037 :
      Shard509.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard509.root_eq_path] using Shard509.valid
  have hvalid038 :
      Shard510.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard510.root_eq_path] using Shard510.valid
  have hvalid039 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid037 hvalid038
  have hvalid040 :
      Shard511.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard511.root_eq_path] using Shard511.valid
  have hvalid041 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid039 hvalid040
  have hvalid042 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hvalid036 hvalid041
  have hvalid043 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid033 hvalid042
  have hvalid044 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid022 hvalid043
  simpa only [tree] using hvalid044

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (4338719621264294493180939 / 4096000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard489.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (89639648503951074869709 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard489.root_eq_path] using Shard489.replay
  have hreplay001 :
      Shard490.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (366575649229895989049883 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard490.root_eq_path] using Shard490.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (89639648503951074869709 / 2048000000000000000000000000 : Rat) + (366575649229895989049883 / 8192000000000000000000000000 : Rat) = (725134243245700288528719 / 8192000000000000000000000000 : Rat))
  have hreplay003 :
      Shard491.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (101630223168173773730991 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard491.root_eq_path] using Shard491.replay
  have hreplay004 :
      Shard492.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (219230543631046869533691 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard492.root_eq_path] using Shard492.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (101630223168173773730991 / 3276800000000000000000000000 : Rat) + (219230543631046869533691 / 8192000000000000000000000000 : Rat) = (946612203102962607722337 / 16384000000000000000000000000 : Rat))
  have hreplay006 :
      Shard493.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (4743562497026251405671 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard493.root_eq_path] using Shard493.replay
  have hreplay007 :
      Shard494.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (403844367567173913579789 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard494.root_eq_path] using Shard494.replay
  have hraw008 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay006 hreplay007
  have hreplay008 := hraw008.trans
    (by norm_num : (4743562497026251405671 / 163840000000000000000000000 : Rat) + (403844367567173913579789 / 16384000000000000000000000000 : Rat) = (878200617269799054146889 / 16384000000000000000000000000 : Rat))
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay005 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (946612203102962607722337 / 16384000000000000000000000000 : Rat) + (878200617269799054146889 / 16384000000000000000000000000 : Rat) = (912406410186380830934613 / 8192000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (725134243245700288528719 / 8192000000000000000000000000 : Rat) + (912406410186380830934613 / 8192000000000000000000000000 : Rat) = (409385163358020279865833 / 2048000000000000000000000000 : Rat))
  have hreplay011 :
      Shard495.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (674338254516118414757853 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard495.root_eq_path] using Shard495.replay
  have hreplay012 :
      Shard496.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (56717266191246315881487 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard496.root_eq_path] using Shard496.replay
  have hreplay013 :
      Shard497.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (380887245200662903328733 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard497.root_eq_path] using Shard497.replay
  have hraw014 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay012 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (56717266191246315881487 / 1024000000000000000000000000 : Rat) + (380887245200662903328733 / 8192000000000000000000000000 : Rat) = (834625374730633430380629 / 8192000000000000000000000000 : Rat))
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay011 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (674338254516118414757853 / 8192000000000000000000000000 : Rat) + (834625374730633430380629 / 8192000000000000000000000000 : Rat) = (754481814623375922569241 / 4096000000000000000000000000 : Rat))
  have hreplay016 :
      Shard498.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (286661047234605998312763 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard498.root_eq_path] using Shard498.replay
  have hreplay017 :
      Shard499.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (235370396879602089954111 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard499.root_eq_path] using Shard499.replay
  have hreplay018 :
      Shard500.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (243047636809046409113469 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard500.root_eq_path] using Shard500.replay
  have hraw019 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay017 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (235370396879602089954111 / 8192000000000000000000000000 : Rat) + (243047636809046409113469 / 8192000000000000000000000000 : Rat) = (23920901684432424953379 / 409600000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay016 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (286661047234605998312763 / 4096000000000000000000000000 : Rat) + (23920901684432424953379 / 409600000000000000000000000 : Rat) = (525870064078930247846553 / 4096000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay015 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (754481814623375922569241 / 4096000000000000000000000000 : Rat) + (525870064078930247846553 / 4096000000000000000000000000 : Rat) = (640175939351153085207897 / 2048000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay010 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (409385163358020279865833 / 2048000000000000000000000000 : Rat) + (640175939351153085207897 / 2048000000000000000000000000 : Rat) = (104956110270917336507373 / 204800000000000000000000000 : Rat))
  have hreplay023 :
      Shard501.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (108073082917142113692771 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard501.root_eq_path] using Shard501.replay
  have hreplay024 :
      Shard502.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (55654153898660575883559 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard502.root_eq_path] using Shard502.replay
  have hraw025 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (108073082917142113692771 / 3276800000000000000000000000 : Rat) + (55654153898660575883559 / 1638400000000000000000000000 : Rat) = (219381390714463265459889 / 3276800000000000000000000000 : Rat))
  have hreplay026 :
      Shard503.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (139140487153656697382037 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard503.root_eq_path] using Shard503.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (219381390714463265459889 / 3276800000000000000000000000 : Rat) + (139140487153656697382037 / 2048000000000000000000000000 : Rat) = (2210030850801569906355741 / 16384000000000000000000000000 : Rat))
  have hreplay028 :
      Shard504.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (190114595761810177060641 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard504.root_eq_path] using Shard504.replay
  have hreplay029 :
      Shard505.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (315185285563288250755203 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard505.root_eq_path] using Shard505.replay
  have hraw030 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (190114595761810177060641 / 4096000000000000000000000000 : Rat) + (315185285563288250755203 / 8192000000000000000000000000 : Rat) = (139082895417381720975297 / 1638400000000000000000000000 : Rat))
  have hreplay031 :
      Shard506.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (445253874960241573809759 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard506.root_eq_path] using Shard506.replay
  have hraw032 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay030 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (139082895417381720975297 / 1638400000000000000000000000 : Rat) + (445253874960241573809759 / 8192000000000000000000000000 : Rat) = (285167088011787544671561 / 2048000000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (e := (4 : Fin 6)) hreplay027 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (2210030850801569906355741 / 16384000000000000000000000000 : Rat) + (285167088011787544671561 / 2048000000000000000000000000 : Rat) = (4491367554895870263728229 / 16384000000000000000000000000 : Rat))
  have hreplay034 :
      Shard507.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (67144294862156670275349 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard507.root_eq_path] using Shard507.replay
  have hreplay035 :
      Shard508.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (223204150280012742080901 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard508.root_eq_path] using Shard508.replay
  have hraw036 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).leftChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay034 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (67144294862156670275349 / 819200000000000000000000000 : Rat) + (223204150280012742080901 / 4096000000000000000000000000 : Rat) = (279462812295398046728823 / 2048000000000000000000000000 : Rat))
  have hreplay037 :
      Shard509.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (364315400373083559973479 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard509.root_eq_path] using Shard509.replay
  have hreplay038 :
      Shard510.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (75215404390198403980179 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard510.root_eq_path] using Shard510.replay
  have hraw039 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay037 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (364315400373083559973479 / 8192000000000000000000000000 : Rat) + (75215404390198403980179 / 2048000000000000000000000000 : Rat) = (133035403586775435178839 / 1638400000000000000000000000 : Rat))
  have hreplay040 :
      Shard511.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (900965574256982062786713 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard511.root_eq_path] using Shard511.replay
  have hraw041 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay039 hreplay040
  have hreplay041 := hraw041.trans
    (by norm_num : (133035403586775435178839 / 1638400000000000000000000000 : Rat) + (900965574256982062786713 / 16384000000000000000000000000 : Rat) = (2231319610124736414575103 / 16384000000000000000000000000 : Rat))
  have hraw042 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (e := (0 : Fin 6)) hreplay036 hreplay041
  have hreplay042 := hraw042.trans
    (by norm_num : (279462812295398046728823 / 2048000000000000000000000000 : Rat) + (2231319610124736414575103 / 16384000000000000000000000000 : Rat) = (4467022108487920788405687 / 16384000000000000000000000000 : Rat))
  have hraw043 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay033 hreplay042
  have hreplay043 := hraw043.trans
    (by norm_num : (4491367554895870263728229 / 16384000000000000000000000000 : Rat) + (4467022108487920788405687 / 16384000000000000000000000000 : Rat) = (2239597415845947763033479 / 4096000000000000000000000000 : Rat))
  have hraw044 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay022 hreplay043
  have hreplay044 := hraw044.trans
    (by norm_num : (104956110270917336507373 / 204800000000000000000000000 : Rat) + (2239597415845947763033479 / 4096000000000000000000000000 : Rat) = (4338719621264294493180939 / 4096000000000000000000000000 : Rat))
  simpa only [tree] using hreplay044

end Branch030
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
