import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard588
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard589
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard590
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard591
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard592
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard593
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard594
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard595
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard596
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard597
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard598
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard599
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard600
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard601
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard602
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard603
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard604
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard605
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard606
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard607
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard608
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard609

/-!
# exact P2 forest branch Branch036
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch036

/- Root 2, exact path ((2, 'right'), (1, 'left'), (3, 'right'), (4, 'left')), 469 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (2 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          Shard588.tree
          (.split (5 : Fin 6)
            Shard589.tree
            Shard590.tree
          )
        )
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            Shard591.tree
            Shard592.tree
          )
          Shard593.tree
        )
      )
      (.split (2 : Fin 6)
        (.split (3 : Fin 6)
          Shard594.tree
          (.split (1 : Fin 6)
            Shard595.tree
            Shard596.tree
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            Shard597.tree
            Shard598.tree
          )
          Shard599.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            Shard600.tree
            Shard601.tree
          )
          Shard602.tree
        )
        (.split (2 : Fin 6)
          Shard603.tree
          Shard604.tree
        )
      )
      (.split (4 : Fin 6)
        (.split (2 : Fin 6)
          Shard605.tree
          (.split (0 : Fin 6)
            Shard606.tree
            Shard607.tree
          )
        )
        (.split (2 : Fin 6)
          Shard608.tree
          Shard609.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard588.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard588.root_eq_path] using Shard588.valid
  have hvalid001 :
      Shard589.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard589.root_eq_path] using Shard589.valid
  have hvalid002 :
      Shard590.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard590.root_eq_path] using Shard590.valid
  have hvalid003 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid001 hvalid002
  have hvalid004 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid003
  have hvalid005 :
      Shard591.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard591.root_eq_path] using Shard591.valid
  have hvalid006 :
      Shard592.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard592.root_eq_path] using Shard592.valid
  have hvalid007 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid005 hvalid006
  have hvalid008 :
      Shard593.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard593.root_eq_path] using Shard593.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hvalid004 hvalid009
  have hvalid011 :
      Shard594.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard594.root_eq_path] using Shard594.valid
  have hvalid012 :
      Shard595.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard595.root_eq_path] using Shard595.valid
  have hvalid013 :
      Shard596.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard596.root_eq_path] using Shard596.valid
  have hvalid014 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid012 hvalid013
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hvalid011 hvalid014
  have hvalid016 :
      Shard597.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard597.root_eq_path] using Shard597.valid
  have hvalid017 :
      Shard598.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard598.root_eq_path] using Shard598.valid
  have hvalid018 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :
      Shard599.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard599.root_eq_path] using Shard599.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hvalid015 hvalid020
  have hvalid022 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid010 hvalid021
  have hvalid023 :
      Shard600.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard600.root_eq_path] using Shard600.valid
  have hvalid024 :
      Shard601.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard601.root_eq_path] using Shard601.valid
  have hvalid025 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :
      Shard602.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard602.root_eq_path] using Shard602.valid
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid025 hvalid026
  have hvalid028 :
      Shard603.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard603.root_eq_path] using Shard603.valid
  have hvalid029 :
      Shard604.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard604.root_eq_path] using Shard604.valid
  have hvalid030 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid027 hvalid030
  have hvalid032 :
      Shard605.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard605.root_eq_path] using Shard605.valid
  have hvalid033 :
      Shard606.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard606.root_eq_path] using Shard606.valid
  have hvalid034 :
      Shard607.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard607.root_eq_path] using Shard607.valid
  have hvalid035 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hvalid033 hvalid034
  have hvalid036 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid032 hvalid035
  have hvalid037 :
      Shard608.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard608.root_eq_path] using Shard608.valid
  have hvalid038 :
      Shard609.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard609.root_eq_path] using Shard609.valid
  have hvalid039 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (2 : Fin 6)) hvalid037 hvalid038
  have hvalid040 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid036 hvalid039
  have hvalid041 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid031 hvalid040
  have hvalid042 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid022 hvalid041
  simpa only [tree] using hvalid042

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (29853130000296677376944457 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard588.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (1180964606917468721117589 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard588.root_eq_path] using Shard588.replay
  have hreplay001 :
      Shard589.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (47570994429262620314859 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard589.root_eq_path] using Shard589.replay
  have hreplay002 :
      Shard590.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (112972897737704901867003 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard590.root_eq_path] using Shard590.replay
  have hraw003 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay001 hreplay002
  have hreplay003 := hraw003.trans
    (by norm_num : (47570994429262620314859 / 1024000000000000000000000000 : Rat) + (112972897737704901867003 / 2048000000000000000000000000 : Rat) = (208114886596230142496721 / 2048000000000000000000000000 : Rat))
  have hraw004 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay003
  have hreplay004 := hraw004.trans
    (by norm_num : (1180964606917468721117589 / 16384000000000000000000000000 : Rat) + (208114886596230142496721 / 2048000000000000000000000000 : Rat) = (2845883699687309861091357 / 16384000000000000000000000000 : Rat))
  have hreplay005 :
      Shard591.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (60125598010871515652589 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard591.root_eq_path] using Shard591.replay
  have hreplay006 :
      Shard592.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (423597354907335593793363 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard592.root_eq_path] using Shard592.replay
  have hraw007 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay005 hreplay006
  have hreplay007 := hraw007.trans
    (by norm_num : (60125598010871515652589 / 1638400000000000000000000000 : Rat) + (423597354907335593793363 / 8192000000000000000000000000 : Rat) = (181056336240423293014077 / 2048000000000000000000000000 : Rat))
  have hreplay008 :
      Shard593.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (366334899135103944512379 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard593.root_eq_path] using Shard593.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (181056336240423293014077 / 2048000000000000000000000000 : Rat) + (366334899135103944512379 / 4096000000000000000000000000 : Rat) = (728447571615950530540533 / 4096000000000000000000000000 : Rat))
  have hraw010 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (e := (4 : Fin 6)) hreplay004 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (2845883699687309861091357 / 16384000000000000000000000000 : Rat) + (728447571615950530540533 / 4096000000000000000000000000 : Rat) = (5759673986151111983253489 / 16384000000000000000000000000 : Rat))
  have hreplay011 :
      Shard594.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (556671186551824326196047 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard594.root_eq_path] using Shard594.replay
  have hreplay012 :
      Shard595.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (77978087307761638246083 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard595.root_eq_path] using Shard595.replay
  have hreplay013 :
      Shard596.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (111298746416949739232307 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard596.root_eq_path] using Shard596.replay
  have hraw014 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)).rightChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay012 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (77978087307761638246083 / 1638400000000000000000000000 : Rat) + (111298746416949739232307 / 2048000000000000000000000000 : Rat) = (835085422206607148159643 / 8192000000000000000000000000 : Rat))
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (2 : Fin 6)) (e := (3 : Fin 6)) hreplay011 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (556671186551824326196047 / 4096000000000000000000000000 : Rat) + (835085422206607148159643 / 8192000000000000000000000000 : Rat) = (1948427795310255800551737 / 8192000000000000000000000000 : Rat))
  have hreplay016 :
      Shard597.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (40923981017624902122909 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard597.root_eq_path] using Shard597.replay
  have hreplay017 :
      Shard598.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (249812890490583196203411 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard598.root_eq_path] using Shard598.replay
  have hraw018 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (40923981017624902122909 / 512000000000000000000000000 : Rat) + (249812890490583196203411 / 4096000000000000000000000000 : Rat) = (577204738631582413186683 / 4096000000000000000000000000 : Rat))
  have hreplay019 :
      Shard599.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (627277662245869340819859 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard599.root_eq_path] using Shard599.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (2 : Fin 6)) (e := (1 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (577204738631582413186683 / 4096000000000000000000000000 : Rat) + (627277662245869340819859 / 4096000000000000000000000000 : Rat) = (602241200438725877003271 / 2048000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (2 : Fin 6)) hreplay015 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (1948427795310255800551737 / 8192000000000000000000000000 : Rat) + (602241200438725877003271 / 2048000000000000000000000000 : Rat) = (4357392597065159308564821 / 8192000000000000000000000000 : Rat))
  have hraw022 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay010 hreplay021
  have hreplay022 := hraw022.trans
    (by norm_num : (5759673986151111983253489 / 16384000000000000000000000000 : Rat) + (4357392597065159308564821 / 8192000000000000000000000000 : Rat) = (14474459180281430600383131 / 16384000000000000000000000000 : Rat))
  have hreplay023 :
      Shard600.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (241264070115529091286681 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard600.root_eq_path] using Shard600.replay
  have hreplay024 :
      Shard601.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (637233114442166422512507 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard601.root_eq_path] using Shard601.replay
  have hraw025 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (241264070115529091286681 / 4096000000000000000000000000 : Rat) + (637233114442166422512507 / 8192000000000000000000000000 : Rat) = (1119761254673224605085869 / 8192000000000000000000000000 : Rat))
  have hreplay026 :
      Shard602.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (123188627542150119519153 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard602.root_eq_path] using Shard602.replay
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay025 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (1119761254673224605085869 / 8192000000000000000000000000 : Rat) + (123188627542150119519153 / 1024000000000000000000000000 : Rat) = (2105270275010425561239093 / 8192000000000000000000000000 : Rat))
  have hreplay028 :
      Shard603.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (29190056340000526890957 / 256000000000000000000000000 : Rat) := by
    simpa only [Shard603.root_eq_path] using Shard603.replay
  have hreplay029 :
      Shard604.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (675242873831407946777991 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard604.root_eq_path] using Shard604.replay
  have hraw030 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (29190056340000526890957 / 256000000000000000000000000 : Rat) + (675242873831407946777991 / 4096000000000000000000000000 : Rat) = (1142283775271416377033303 / 4096000000000000000000000000 : Rat))
  have hraw031 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay027 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (2105270275010425561239093 / 8192000000000000000000000000 : Rat) + (1142283775271416377033303 / 4096000000000000000000000000 : Rat) = (4389837825553258315305699 / 8192000000000000000000000000 : Rat))
  have hreplay032 :
      Shard605.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (127251385979841184317579 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard605.root_eq_path] using Shard605.replay
  have hreplay033 :
      Shard606.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (401318036472677096379573 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard606.root_eq_path] using Shard606.replay
  have hreplay034 :
      Shard607.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (592370538139157313792933 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard607.root_eq_path] using Shard607.replay
  have hraw035 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (2 : Fin 6)) (e := (0 : Fin 6)) hreplay033 hreplay034
  have hreplay035 := hraw035.trans
    (by norm_num : (401318036472677096379573 / 8192000000000000000000000000 : Rat) + (592370538139157313792933 / 8192000000000000000000000000 : Rat) = (496844287305917205086253 / 4096000000000000000000000000 : Rat))
  have hraw036 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay032 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (127251385979841184317579 / 1638400000000000000000000000 : Rat) + (496844287305917205086253 / 4096000000000000000000000000 : Rat) = (1629945504511040331760401 / 8192000000000000000000000000 : Rat))
  have hreplay037 :
      Shard608.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (13015955439637541811081 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard608.root_eq_path] using Shard608.replay
  have hreplay038 :
      Shard609.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (1018754307961447650660513 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard609.root_eq_path] using Shard609.replay
  have hraw039 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (2 : Fin 6)) hreplay037 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (13015955439637541811081 / 163840000000000000000000000 : Rat) + (1018754307961447650660513 / 8192000000000000000000000000 : Rat) = (1669552079943324741214563 / 8192000000000000000000000000 : Rat))
  have hraw040 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay036 hreplay039
  have hreplay040 := hraw040.trans
    (by norm_num : (1629945504511040331760401 / 8192000000000000000000000000 : Rat) + (1669552079943324741214563 / 8192000000000000000000000000 : Rat) = (824874396113591268243741 / 2048000000000000000000000000 : Rat))
  have hraw041 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay031 hreplay040
  have hreplay041 := hraw041.trans
    (by norm_num : (4389837825553258315305699 / 8192000000000000000000000000 : Rat) + (824874396113591268243741 / 2048000000000000000000000000 : Rat) = (7689335410007623388280663 / 8192000000000000000000000000 : Rat))
  have hraw042 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).rightChild (2 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay022 hreplay041
  have hreplay042 := hraw042.trans
    (by norm_num : (14474459180281430600383131 / 16384000000000000000000000000 : Rat) + (7689335410007623388280663 / 8192000000000000000000000000 : Rat) = (29853130000296677376944457 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay042

end Branch036
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
