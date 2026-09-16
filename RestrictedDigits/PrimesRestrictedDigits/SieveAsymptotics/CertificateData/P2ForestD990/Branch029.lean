import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard465
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard466
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard467
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard468
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard469
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard470
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard471
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard472
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard473
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard474
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard475
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard476
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard477
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard478
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard479
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard480
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard481
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard482
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard483
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard484
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard485
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard486
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard487
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Shard488

/-!
# exact P2 forest branch Branch029
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch029

/- Root 2, exact path ((2, 'left'), (4, 'right'), (3, 'left'), (3, 'right')), 522 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (4 : Fin 6)
    (.split (5 : Fin 6)
      (.split (4 : Fin 6)
        (.split (5 : Fin 6)
          (.split (2 : Fin 6)
            Shard465.tree
            Shard466.tree
          )
          (.split (1 : Fin 6)
            Shard467.tree
            Shard468.tree
          )
        )
        (.split (1 : Fin 6)
          Shard469.tree
          (.split (1 : Fin 6)
            Shard470.tree
            Shard471.tree
          )
        )
      )
      (.split (1 : Fin 6)
        (.split (3 : Fin 6)
          Shard472.tree
          Shard473.tree
        )
        (.split (2 : Fin 6)
          Shard474.tree
          Shard475.tree
        )
      )
    )
    (.split (3 : Fin 6)
      (.split (1 : Fin 6)
        (.split (5 : Fin 6)
          (.split (5 : Fin 6)
            Shard476.tree
            Shard477.tree
          )
          (.split (3 : Fin 6)
            Shard478.tree
            Shard479.tree
          )
        )
        (.split (0 : Fin 6)
          (.split (5 : Fin 6)
            Shard480.tree
            Shard481.tree
          )
          Shard482.tree
        )
      )
      (.split (0 : Fin 6)
        (.split (3 : Fin 6)
          (.split (1 : Fin 6)
            Shard483.tree
            Shard484.tree
          )
          (.split (4 : Fin 6)
            Shard485.tree
            Shard486.tree
          )
        )
        (.split (1 : Fin 6)
          Shard487.tree
          Shard488.tree
        )
      )
    )
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) = true := by
  have hvalid000 :
      Shard465.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard465.root_eq_path] using Shard465.valid
  have hvalid001 :
      Shard466.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard466.root_eq_path] using Shard466.valid
  have hvalid002 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hvalid000 hvalid001
  have hvalid003 :
      Shard467.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard467.root_eq_path] using Shard467.valid
  have hvalid004 :
      Shard468.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard468.root_eq_path] using Shard468.valid
  have hvalid005 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid003 hvalid004
  have hvalid006 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid002 hvalid005
  have hvalid007 :
      Shard469.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard469.root_eq_path] using Shard469.valid
  have hvalid008 :
      Shard470.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard470.root_eq_path] using Shard470.valid
  have hvalid009 :
      Shard471.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard471.root_eq_path] using Shard471.valid
  have hvalid010 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hvalid008 hvalid009
  have hvalid011 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hvalid007 hvalid010
  have hvalid012 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hvalid006 hvalid011
  have hvalid013 :
      Shard472.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard472.root_eq_path] using Shard472.valid
  have hvalid014 :
      Shard473.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard473.root_eq_path] using Shard473.valid
  have hvalid015 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hvalid013 hvalid014
  have hvalid016 :
      Shard474.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) = true := by
    simpa only [Shard474.root_eq_path] using Shard474.valid
  have hvalid017 :
      Shard475.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) = true := by
    simpa only [Shard475.root_eq_path] using Shard475.valid
  have hvalid018 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hvalid016 hvalid017
  have hvalid019 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hvalid015 hvalid018
  have hvalid020 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid012 hvalid019
  have hvalid021 :
      Shard476.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard476.root_eq_path] using Shard476.valid
  have hvalid022 :
      Shard477.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard477.root_eq_path] using Shard477.valid
  have hvalid023 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hvalid021 hvalid022
  have hvalid024 :
      Shard478.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) = true := by
    simpa only [Shard478.root_eq_path] using Shard478.valid
  have hvalid025 :
      Shard479.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) = true := by
    simpa only [Shard479.root_eq_path] using Shard479.valid
  have hvalid026 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hvalid024 hvalid025
  have hvalid027 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hvalid023 hvalid026
  have hvalid028 :
      Shard480.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    simpa only [Shard480.root_eq_path] using Shard480.valid
  have hvalid029 :
      Shard481.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    simpa only [Shard481.root_eq_path] using Shard481.valid
  have hvalid030 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (5 : Fin 6)) hvalid028 hvalid029
  have hvalid031 :
      Shard482.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) = true := by
    simpa only [Shard482.root_eq_path] using Shard482.valid
  have hvalid032 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hvalid030 hvalid031
  have hvalid033 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid027 hvalid032
  have hvalid034 :
      Shard483.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard483.root_eq_path] using Shard483.valid
  have hvalid035 :
      Shard484.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard484.root_eq_path] using Shard484.valid
  have hvalid036 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hvalid034 hvalid035
  have hvalid037 :
      Shard485.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) = true := by
    simpa only [Shard485.root_eq_path] using Shard485.valid
  have hvalid038 :
      Shard486.tree.coverValid sectionSixP2LeafValidD988 ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) = true := by
    simpa only [Shard486.root_eq_path] using Shard486.valid
  have hvalid039 :=
    valid_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid037 hvalid038
  have hvalid040 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hvalid036 hvalid039
  have hvalid041 :
      Shard487.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) = true := by
    simpa only [Shard487.root_eq_path] using Shard487.valid
  have hvalid042 :
      Shard488.tree.coverValid sectionSixP2LeafValidD988 (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) = true := by
    simpa only [Shard488.root_eq_path] using Shard488.valid
  have hvalid043 :=
    valid_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hvalid041 hvalid042
  have hvalid044 :=
    valid_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hvalid040 hvalid043
  have hvalid045 :=
    valid_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hvalid033 hvalid044
  have hvalid046 :=
    valid_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hvalid020 hvalid045
  simpa only [tree] using hvalid046

theorem replay :
    tree.replayWeightRat (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
      (5199870362530362664125051 / 3276800000000000000000000000 : Rat) := by
  have hreplay000 :
      Shard465.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (15935755580664530724729 / 655360000000000000000000000 : Rat) := by
    simpa only [Shard465.root_eq_path] using Shard465.replay
  have hreplay001 :
      Shard466.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (105591267934236807873381 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard466.root_eq_path] using Shard466.replay
  have hraw002 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (2 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (15935755580664530724729 / 655360000000000000000000000 : Rat) + (105591267934236807873381 / 4096000000000000000000000000 : Rat) = (820758961253560499611749 / 16384000000000000000000000000 : Rat))
  have hreplay003 :
      Shard467.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (3617782858393614875007 / 102400000000000000000000000 : Rat) := by
    simpa only [Shard467.root_eq_path] using Shard467.replay
  have hreplay004 :
      Shard468.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (15114834470195904419577 / 512000000000000000000000000 : Rat) := by
    simpa only [Shard468.root_eq_path] using Shard468.replay
  have hraw005 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay003 hreplay004
  have hreplay005 := hraw005.trans
    (by norm_num : (3617782858393614875007 / 102400000000000000000000000 : Rat) + (15114834470195904419577 / 512000000000000000000000000 : Rat) = (8300937190540994698653 / 128000000000000000000000000 : Rat))
  have hraw006 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay002 hreplay005
  have hreplay006 := hraw006.trans
    (by norm_num : (820758961253560499611749 / 16384000000000000000000000000 : Rat) + (8300937190540994698653 / 128000000000000000000000000 : Rat) = (1883278921642807821039333 / 16384000000000000000000000000 : Rat))
  have hreplay007 :
      Shard469.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (620007095779380129550149 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard469.root_eq_path] using Shard469.replay
  have hreplay008 :
      Shard470.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (136219070102449654819053 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard470.root_eq_path] using Shard470.replay
  have hreplay009 :
      Shard471.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (248269110916682030877099 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard471.root_eq_path] using Shard471.replay
  have hraw010 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)).rightChild (1 : Fin 6)) (e := (1 : Fin 6)) hreplay008 hreplay009
  have hreplay010 := hraw010.trans
    (by norm_num : (136219070102449654819053 / 4096000000000000000000000000 : Rat) + (248269110916682030877099 / 8192000000000000000000000000 : Rat) = (104141450224316268103041 / 1638400000000000000000000000 : Rat))
  have hraw011 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)).rightChild (4 : Fin 6)) (e := (1 : Fin 6)) hreplay007 hreplay010
  have hreplay011 := hraw011.trans
    (by norm_num : (620007095779380129550149 / 8192000000000000000000000000 : Rat) + (104141450224316268103041 / 1638400000000000000000000000 : Rat) = (570357173450480735032677 / 4096000000000000000000000000 : Rat))
  have hraw012 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (e := (4 : Fin 6)) hreplay006 hreplay011
  have hreplay012 := hraw012.trans
    (by norm_num : (1883278921642807821039333 / 16384000000000000000000000000 : Rat) + (570357173450480735032677 / 4096000000000000000000000000 : Rat) = (4164707615444730761170041 / 16384000000000000000000000000 : Rat))
  have hreplay013 :
      Shard472.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (264265934372980377136623 / 2048000000000000000000000000 : Rat) := by
    simpa only [Shard472.root_eq_path] using Shard472.replay
  have hreplay014 :
      Shard473.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (853281722370025138834431 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard473.root_eq_path] using Shard473.replay
  have hraw015 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).leftChild (1 : Fin 6)) (e := (3 : Fin 6)) hreplay013 hreplay014
  have hreplay015 := hraw015.trans
    (by norm_num : (264265934372980377136623 / 2048000000000000000000000000 : Rat) + (853281722370025138834431 / 8192000000000000000000000000 : Rat) = (1910345459861946647380923 / 8192000000000000000000000000 : Rat))
  have hreplay016 :
      Shard474.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)) (fun _ p => p.upper) =
        (363840584152339896793119 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard474.root_eq_path] using Shard474.replay
  have hreplay017 :
      Shard475.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)).rightChild (2 : Fin 6)) (fun _ p => p.upper) =
        (625135539044057338872279 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard475.root_eq_path] using Shard475.replay
  have hraw018 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)).rightChild (1 : Fin 6)) (e := (2 : Fin 6)) hreplay016 hreplay017
  have hreplay018 := hraw018.trans
    (by norm_num : (363840584152339896793119 / 4096000000000000000000000000 : Rat) + (625135539044057338872279 / 8192000000000000000000000000 : Rat) = (1352816707348737132458517 / 8192000000000000000000000000 : Rat))
  have hraw019 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (e := (1 : Fin 6)) hreplay015 hreplay018
  have hreplay019 := hraw019.trans
    (by norm_num : (1910345459861946647380923 / 8192000000000000000000000000 : Rat) + (1352816707348737132458517 / 8192000000000000000000000000 : Rat) = (40789527090133547247993 / 102400000000000000000000000 : Rat))
  have hraw020 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay012 hreplay019
  have hreplay020 := hraw020.trans
    (by norm_num : (4164707615444730761170041 / 16384000000000000000000000000 : Rat) + (40789527090133547247993 / 102400000000000000000000000 : Rat) = (10691031949866098320848921 / 16384000000000000000000000000 : Rat))
  have hreplay021 :
      Shard476.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (48384095773249960994511 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard476.root_eq_path] using Shard476.replay
  have hreplay022 :
      Shard477.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (53847310254402672214857 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard477.root_eq_path] using Shard477.replay
  have hraw023 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).leftChild (5 : Fin 6)) (e := (5 : Fin 6)) hreplay021 hreplay022
  have hreplay023 := hraw023.trans
    (by norm_num : (48384095773249960994511 / 819200000000000000000000000 : Rat) + (53847310254402672214857 / 819200000000000000000000000 : Rat) = (12778925753456579151171 / 102400000000000000000000000 : Rat))
  have hreplay024 :
      Shard478.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).leftChild (3 : Fin 6)) (fun _ p => p.upper) =
        (314497735989612418638387 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard478.root_eq_path] using Shard478.replay
  have hreplay025 :
      Shard479.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)).rightChild (3 : Fin 6)) (fun _ p => p.upper) =
        (62265485697091750161351 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard479.root_eq_path] using Shard479.replay
  have hraw026 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)).rightChild (5 : Fin 6)) (e := (3 : Fin 6)) hreplay024 hreplay025
  have hreplay026 := hraw026.trans
    (by norm_num : (314497735989612418638387 / 4096000000000000000000000000 : Rat) + (62265485697091750161351 / 819200000000000000000000000 : Rat) = (312912582237535584722571 / 2048000000000000000000000000 : Rat))
  have hraw027 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (e := (5 : Fin 6)) hreplay023 hreplay026
  have hreplay027 := hraw027.trans
    (by norm_num : (12778925753456579151171 / 102400000000000000000000000 : Rat) + (312912582237535584722571 / 2048000000000000000000000000 : Rat) = (568491097306667167745991 / 2048000000000000000000000000 : Rat))
  have hreplay028 :
      Shard480.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (46506298530826013150259 / 819200000000000000000000000 : Rat) := by
    simpa only [Shard480.root_eq_path] using Shard480.replay
  have hreplay029 :
      Shard481.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (98441866667854543215627 / 1638400000000000000000000000 : Rat) := by
    simpa only [Shard481.root_eq_path] using Shard481.replay
  have hraw030 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).leftChild (0 : Fin 6)) (e := (5 : Fin 6)) hreplay028 hreplay029
  have hreplay030 := hraw030.trans
    (by norm_num : (46506298530826013150259 / 819200000000000000000000000 : Rat) + (98441866667854543215627 / 1638400000000000000000000000 : Rat) = (38290892745901313903229 / 327680000000000000000000000 : Rat))
  have hreplay031 :
      Shard482.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)).rightChild (0 : Fin 6)) (fun _ p => p.upper) =
        (1374129130672956393750753 / 16384000000000000000000000000 : Rat) := by
    simpa only [Shard482.root_eq_path] using Shard482.replay
  have hraw032 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (e := (0 : Fin 6)) hreplay030 hreplay031
  have hreplay032 := hraw032.trans
    (by norm_num : (38290892745901313903229 / 327680000000000000000000000 : Rat) + (1374129130672956393750753 / 16384000000000000000000000000 : Rat) = (3288673767968022088912203 / 16384000000000000000000000000 : Rat))
  have hraw033 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay027 hreplay032
  have hreplay033 := hraw033.trans
    (by norm_num : (568491097306667167745991 / 2048000000000000000000000000 : Rat) + (3288673767968022088912203 / 16384000000000000000000000000 : Rat) = (7836602546421359430880131 / 16384000000000000000000000000 : Rat))
  have hreplay034 :
      Shard483.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (295114840457204012748309 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard483.root_eq_path] using Shard483.replay
  have hreplay035 :
      Shard484.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (496156352332143714978609 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard484.root_eq_path] using Shard484.replay
  have hraw036 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).leftChild (3 : Fin 6)) (e := (1 : Fin 6)) hreplay034 hreplay035
  have hreplay036 := hraw036.trans
    (by norm_num : (295114840457204012748309 / 4096000000000000000000000000 : Rat) + (496156352332143714978609 / 8192000000000000000000000000 : Rat) = (1086386033246551740475227 / 8192000000000000000000000000 : Rat))
  have hreplay037 :
      Shard485.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
        (240460827078010200735591 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard485.root_eq_path] using Shard485.replay
  have hreplay038 :
      Shard486.tree.replayWeightRat ((((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (fun _ p => p.upper) =
        (290438013272514310850769 / 4096000000000000000000000000 : Rat) := by
    simpa only [Shard486.root_eq_path] using Shard486.replay
  have hraw039 :=
    replay_split (T := ((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay037 hreplay038
  have hreplay039 := hraw039.trans
    (by norm_num : (240460827078010200735591 / 4096000000000000000000000000 : Rat) + (290438013272514310850769 / 4096000000000000000000000000 : Rat) = (13272471008763112789659 / 102400000000000000000000000 : Rat))
  have hraw040 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).leftChild (0 : Fin 6)) (e := (3 : Fin 6)) hreplay036 hreplay039
  have hreplay040 := hraw040.trans
    (by norm_num : (1086386033246551740475227 / 8192000000000000000000000000 : Rat) + (13272471008763112789659 / 102400000000000000000000000 : Rat) = (2148183713947600763647947 / 8192000000000000000000000000 : Rat))
  have hreplay041 :
      Shard487.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).leftChild (1 : Fin 6)) (fun _ p => p.upper) =
        (931379279244980604246837 / 8192000000000000000000000000 : Rat) := by
    simpa only [Shard487.root_eq_path] using Shard487.replay
  have hreplay042 :
      Shard488.tree.replayWeightRat (((((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)).rightChild (1 : Fin 6)) (fun _ p => p.upper) =
        (262518265995838566621327 / 3276800000000000000000000000 : Rat) := by
    simpa only [Shard488.root_eq_path] using Shard488.replay
  have hraw043 :=
    replay_split (T := (((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)).rightChild (0 : Fin 6)) (e := (1 : Fin 6)) hreplay041 hreplay042
  have hreplay043 := hraw043.trans
    (by norm_num : (931379279244980604246837 / 8192000000000000000000000000 : Rat) + (262518265995838566621327 / 3276800000000000000000000000 : Rat) = (3175349888469154041600309 / 16384000000000000000000000000 : Rat))
  have hraw044 :=
    replay_split (T := ((((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)).rightChild (3 : Fin 6)) (e := (0 : Fin 6)) hreplay040 hreplay043
  have hreplay044 := hraw044.trans
    (by norm_num : (2148183713947600763647947 / 8192000000000000000000000000 : Rat) + (3175349888469154041600309 / 16384000000000000000000000000 : Rat) = (7471717316364355568896203 / 16384000000000000000000000000 : Rat))
  have hraw045 :=
    replay_split (T := (((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)).rightChild (4 : Fin 6)) (e := (3 : Fin 6)) hreplay033 hreplay044
  have hreplay045 := hraw045.trans
    (by norm_num : (7836602546421359430880131 / 16384000000000000000000000000 : Rat) + (7471717316364355568896203 / 16384000000000000000000000000 : Rat) = (7654159931392857499888167 / 8192000000000000000000000000 : Rat))
  have hraw046 :=
    replay_split (T := ((((sectionSixP2RootD974 (2 : Fin 3)).leftChild (2 : Fin 6)).rightChild (4 : Fin 6)).leftChild (3 : Fin 6)).rightChild (3 : Fin 6)) (e := (4 : Fin 6)) hreplay020 hreplay045
  have hreplay046 := hraw046.trans
    (by norm_num : (10691031949866098320848921 / 16384000000000000000000000000 : Rat) + (7654159931392857499888167 / 8192000000000000000000000000 : Rat) = (5199870362530362664125051 / 3276800000000000000000000000 : Rat))
  simpa only [tree] using hreplay046

end Branch029
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
