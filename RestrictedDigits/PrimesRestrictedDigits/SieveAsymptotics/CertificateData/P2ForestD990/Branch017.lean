import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard273
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard274
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard275
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard276
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard277
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard278
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard279
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard280
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard281
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard282
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard283
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard284
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard285
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard286
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard287
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard288
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard289
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard290
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard291
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard292
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard293
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard294
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard295
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard296

/-!
# exact P2 forest branch Branch017
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch017

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'right')), 583 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (3 : Fin 6)
    (.split (4 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            Shard273.tree
            Shard274.tree
          )
          (.split (1 : Fin 6)
            Shard275.tree
            Shard276.tree
          )
        )
        (.split (1 : Fin 6)
          (.split (3 : Fin 6)
            Shard277.tree
            Shard278.tree
          )
          (.split (4 : Fin 6)
            Shard279.tree
            Shard280.tree
          )
        )
      )
      (.split (3 : Fin 6)
        (.split (3 : Fin 6)
          (.split (5 : Fin 6)
            Shard281.tree
            Shard282.tree
          )
          (.split (0 : Fin 6)
            Shard283.tree
            Shard284.tree
          )
        )
        (.split (0 : Fin 6)
          Shard285.tree
          (.split (1 : Fin 6)
            Shard286.tree
            Shard287.tree
          )
        )
      )
    )
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (4 : Fin 6)
          (.split (5 : Fin 6)
            Shard288.tree
            Shard289.tree
          )
          Shard290.tree
        )
        (.split (0 : Fin 6)
          Shard291.tree
          Shard292.tree
        )
      )
      (.split (0 : Fin 6)
        Shard293.tree
        (.split (1 : Fin 6)
          Shard294.tree
          (.split (0 : Fin 6)
            Shard295.tree
            Shard296.tree
          )
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Shard273.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard273.root_eq_path] using Shard273.valid
  have hvalid001 :
      Shard274.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard274.root_eq_path] using Shard274.valid
  have hvalid002 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard275.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard275.root_eq_path] using Shard275.valid
  have hvalid004 :
      Shard276.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard276.root_eq_path] using Shard276.valid
  have hvalid005 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard277.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard277.root_eq_path] using Shard277.valid
  have hvalid008 :
      Shard278.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard278.root_eq_path] using Shard278.valid
  have hvalid009 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid007 hvalid008
  have hvalid010 :
      Shard279.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard279.root_eq_path] using Shard279.valid
  have hvalid011 :
      Shard280.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard280.root_eq_path] using Shard280.valid
  have hvalid012 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hvalid010 hvalid011
  have hvalid013 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid009 hvalid012
  have hvalid014 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid013
  have hvalid015 :
      Shard281.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard281.root_eq_path] using Shard281.valid
  have hvalid016 :
      Shard282.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard282.root_eq_path] using Shard282.valid
  have hvalid017 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid015 hvalid016
  have hvalid018 :
      Shard283.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard283.root_eq_path] using Shard283.valid
  have hvalid019 :
      Shard284.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard284.root_eq_path] using Shard284.valid
  have hvalid020 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid018 hvalid019
  have hvalid021 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hvalid017 hvalid020
  have hvalid022 :
      Shard285.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard285.root_eq_path] using Shard285.valid
  have hvalid023 :
      Shard286.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard286.root_eq_path] using Shard286.valid
  have hvalid024 :
      Shard287.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard287.root_eq_path] using Shard287.valid
  have hvalid025 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid023 hvalid024
  have hvalid026 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid022 hvalid025
  have hvalid027 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid021 hvalid026
  have hvalid028 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid014 hvalid027
  have hvalid029 :
      Shard288.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard288.root_eq_path] using Shard288.valid
  have hvalid030 :
      Shard289.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard289.root_eq_path] using Shard289.valid
  have hvalid031 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid029 hvalid030
  have hvalid032 :
      Shard290.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard290.root_eq_path] using Shard290.valid
  have hvalid033 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hvalid031 hvalid032
  have hvalid034 :
      Shard291.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard291.root_eq_path] using Shard291.valid
  have hvalid035 :
      Shard292.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard292.root_eq_path] using Shard292.valid
  have hvalid036 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hvalid034 hvalid035
  have hvalid037 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid033 hvalid036
  have hvalid038 :
      Shard293.tree.coverValid sectionSixP2LeafValidD988 (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard293.root_eq_path] using Shard293.valid
  have hvalid039 :
      Shard294.tree.coverValid sectionSixP2LeafValidD988 ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard294.root_eq_path] using Shard294.valid
  have hvalid040 :
      Shard295.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) = true := by
    simpa only [Shard295.root_eq_path] using Shard295.valid
  have hvalid041 :
      Shard296.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard296.root_eq_path] using Shard296.valid
  have hvalid042 :=
    valid_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid040 hvalid041
  have hvalid043 :=
    valid_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid039 hvalid042
  have hvalid044 :=
    valid_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hvalid038 hvalid043
  have hvalid045 :=
    valid_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (5 : Fin 6)) hvalid037 hvalid044
  have hvalid046 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid028 hvalid045
  simpa only [tree] using hvalid046

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
      (4594703345088479150601573 / 16384000000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard273.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (65471190224496946682247 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard273.root_eq_path] using Shard273.replay
  have hreplay001 :
      Shard274.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (33929379677462128319637 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard274.root_eq_path] using Shard274.replay
  have hraw002 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (65471190224496946682247 / 16384000000000000000000000000 : Rat) + (33929379677462128319637 / 8192000000000000000000000000 : Rat) = (133329949579421203321521 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard275.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (23753079638922799100979 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard275.root_eq_path] using Shard275.replay
  have hreplay004 :
      Shard276.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (7883257002583184356509 / 1024000000000000000000000000 : Rat) := by
    simpa only [Shard276.root_eq_path] using Shard276.replay
  have hraw005 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (23753079638922799100979 / 1638400000000000000000000000 : Rat) + (7883257002583184356509 / 1024000000000000000000000000 : Rat) = (181831454215279470356967 / 8192000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (133329949579421203321521 / 16384000000000000000000000000 : Rat) + (181831454215279470356967 / 8192000000000000000000000000 : Rat) = (99398571601996028807091 / 3276800000000000000000000000 : Rat))
  have hreplay007 :
      Shard277.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (131570621279860857394473 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard277.root_eq_path] using Shard277.replay
  have hreplay008 :
      Shard278.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (36474553261510430201829 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard278.root_eq_path] using Shard278.replay
  have hraw009 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay007 hreplay008
  have hreplay009 := hraw009.trans
    (by norm_num : (131570621279860857394473 / 8192000000000000000000000000 : Rat) + (36474553261510430201829 / 3276800000000000000000000000 : Rat) = (445514008867273865798091 / 16384000000000000000000000000 : Rat))
  have hreplay010 :
      Shard279.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (95191974706286569900437 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard279.root_eq_path] using Shard279.replay
  have hreplay011 :
      Shard280.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (115060067725773005633781 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard280.root_eq_path] using Shard280.replay
  have hraw012 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (4 : Fin 6)) hreplay010 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (95191974706286569900437 / 16384000000000000000000000000 : Rat) + (115060067725773005633781 / 16384000000000000000000000000 : Rat) = (105126021216029787767109 / 8192000000000000000000000000 : Rat))
  have hraw013 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay009 hreplay012
  have hreplay013 := hraw013.trans
    (by norm_num : (445514008867273865798091 / 16384000000000000000000000000 : Rat) + (105126021216029787767109 / 8192000000000000000000000000 : Rat) = (655766051299333441332309 / 16384000000000000000000000000 : Rat))
  have hraw014 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay013
  have hreplay014 := hraw014.trans
    (by norm_num : (99398571601996028807091 / 3276800000000000000000000000 : Rat) + (655766051299333441332309 / 16384000000000000000000000000 : Rat) = (288189727327328396341941 / 4096000000000000000000000000 : Rat))
  have hreplay015 :
      Shard281.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (7016868523815739628103 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard281.root_eq_path] using Shard281.replay
  have hreplay016 :
      Shard282.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (38589333897457459956051 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard282.root_eq_path] using Shard282.replay
  have hraw017 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay015 hreplay016
  have hreplay017 := hraw017.trans
    (by norm_num : (7016868523815739628103 / 512000000000000000000000000 : Rat) + (38589333897457459956051 / 2048000000000000000000000000 : Rat) = (66656807992720418468463 / 2048000000000000000000000000 : Rat))
  have hreplay018 :
      Shard283.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (156351563491659847332057 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard283.root_eq_path] using Shard283.replay
  have hreplay019 :
      Shard284.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (39438824744141522229087 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard284.root_eq_path] using Shard284.replay
  have hraw020 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay018 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (156351563491659847332057 / 8192000000000000000000000000 : Rat) + (39438824744141522229087 / 3276800000000000000000000000 : Rat) = (509897250704027305809549 / 16384000000000000000000000000 : Rat))
  have hraw021 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (3 : Fin 6)) hreplay017 hreplay020
  have hreplay021 := hraw021.trans
    (by norm_num : (66656807992720418468463 / 2048000000000000000000000000 : Rat) + (509897250704027305809549 / 16384000000000000000000000000 : Rat) = (1043151714645790653557253 / 16384000000000000000000000000 : Rat))
  have hreplay022 :
      Shard285.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (564337426033163740372173 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard285.root_eq_path] using Shard285.replay
  have hreplay023 :
      Shard286.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (935047537160179263363 / 65536000000000000000000000 : Rat) := by
    simpa only [Shard286.root_eq_path] using Shard286.replay
  have hreplay024 :
      Shard287.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (29644788904058387704617 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard287.root_eq_path] using Shard287.replay
  have hraw025 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay023 hreplay024
  have hreplay025 := hraw025.trans
    (by norm_num : (935047537160179263363 / 65536000000000000000000000 : Rat) + (29644788904058387704617 / 4096000000000000000000000000 : Rat) = (176170519953139183329609 / 8192000000000000000000000000 : Rat))
  have hraw026 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay022 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (564337426033163740372173 / 16384000000000000000000000000 : Rat) + (176170519953139183329609 / 8192000000000000000000000000 : Rat) = (916678465939442107031391 / 16384000000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay021 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (1043151714645790653557253 / 16384000000000000000000000000 : Rat) + (916678465939442107031391 / 16384000000000000000000000000 : Rat) = (489957545146308190147161 / 4096000000000000000000000000 : Rat))
  have hraw028 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay014 hreplay027
  have hreplay028 := hraw028.trans
    (by norm_num : (288189727327328396341941 / 4096000000000000000000000000 : Rat) + (489957545146308190147161 / 4096000000000000000000000000 : Rat) = (389073636236818293244551 / 2048000000000000000000000000 : Rat))
  have hreplay029 :
      Shard288.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (7813657458692987914683 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard288.root_eq_path] using Shard288.replay
  have hreplay030 :
      Shard289.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (23872212624705327749079 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard289.root_eq_path] using Shard289.replay
  have hraw031 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay029 hreplay030
  have hreplay031 := hraw031.trans
    (by norm_num : (7813657458692987914683 / 8192000000000000000000000000 : Rat) + (23872212624705327749079 / 8192000000000000000000000000 : Rat) = (15842935041699157831881 / 4096000000000000000000000000 : Rat))
  have hreplay032 :
      Shard290.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (71372203608984427316043 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard290.root_eq_path] using Shard290.replay
  have hraw033 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (4 : Fin 6)) hreplay031 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (15842935041699157831881 / 4096000000000000000000000000 : Rat) + (71372203608984427316043 / 16384000000000000000000000000 : Rat) = (134743943775781058643567 / 16384000000000000000000000000 : Rat))
  have hreplay034 :
      Shard291.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (12749429882927718301923 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard291.root_eq_path] using Shard291.replay
  have hreplay035 :
      Shard292.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (19927922700016790762643 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard292.root_eq_path] using Shard292.replay
  have hraw036 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (0 : Fin 6)) hreplay034 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (12749429882927718301923 / 2048000000000000000000000000 : Rat) + (19927922700016790762643 / 4096000000000000000000000000 : Rat) = (45426782465872227366489 / 4096000000000000000000000000 : Rat))
  have hraw037 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay033 hreplay036
  have hreplay037 := hraw037.trans
    (by norm_num : (134743943775781058643567 / 16384000000000000000000000000 : Rat) + (45426782465872227366489 / 4096000000000000000000000000 : Rat) = (316451073639269968109523 / 16384000000000000000000000000 : Rat))
  have hreplay038 :
      Shard293.tree.replayWeightRat (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (664596695952860867172351 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard293.root_eq_path] using Shard293.replay
  have hreplay039 :
      Shard294.tree.replayWeightRat ((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (348929257518198011045583 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard294.root_eq_path] using Shard294.replay
  have hreplay040 :
      Shard295.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (fun _ p => p.upper) =
        (9974652324891579070551 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard295.root_eq_path] using Shard295.replay
  have hreplay041 :
      Shard296.tree.replayWeightRat (((((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (723400094844713257533 / 163840000000000000000000000 : Rat) := by
    simpa only [Shard296.root_eq_path] using Shard296.replay
  have hraw042 :=
    replay_split (T := (((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay040 hreplay041
  have hreplay042 := hraw042.trans
    (by norm_num : (9974652324891579070551 / 2048000000000000000000000000 : Rat) + (723400094844713257533 / 163840000000000000000000000 : Rat) = (38034307020900989579427 / 4096000000000000000000000000 : Rat))
  have hraw043 :=
    replay_split (T := ((((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay039 hreplay042
  have hreplay043 := hraw043.trans
    (by norm_num : (348929257518198011045583 / 16384000000000000000000000000 : Rat) + (38034307020900989579427 / 4096000000000000000000000000 : Rat) = (501066485601801969363291 / 16384000000000000000000000000 : Rat))
  have hraw044 :=
    replay_split (T := (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (5 : Fin 6)) (e := (0 : Fin 6)) hreplay038 hreplay043
  have hreplay044 := hraw044.trans
    (by norm_num : (664596695952860867172351 / 16384000000000000000000000000 : Rat) + (501066485601801969363291 / 16384000000000000000000000000 : Rat) = (582831590777331418267821 / 8192000000000000000000000000 : Rat))
  have hraw045 :=
    replay_split (T := ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (5 : Fin 6)) hreplay037 hreplay044
  have hreplay045 := hraw045.trans
    (by norm_num : (316451073639269968109523 / 16384000000000000000000000000 : Rat) + (582831590777331418267821 / 8192000000000000000000000000 : Rat) = (296422851038786560929033 / 3276800000000000000000000000 : Rat))
  have hraw046 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay028 hreplay045
  have hreplay046 := hraw046.trans
    (by norm_num : (389073636236818293244551 / 2048000000000000000000000000 : Rat) + (296422851038786560929033 / 3276800000000000000000000000 : Rat) = (4594703345088479150601573 / 16384000000000000000000000000 : Rat))
  simpa only [tree] using hreplay046

end Branch017
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
