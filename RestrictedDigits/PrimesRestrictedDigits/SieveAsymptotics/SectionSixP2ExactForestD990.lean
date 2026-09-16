import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Root0
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Root1
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Root2
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafValidatorD989

/-!
# Exact forest certificate for the original P2 profile

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). The imported shards check every leaf
payload, original root path and replay.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

open SectionSixP2CertificateD990

def sectionSixP2ForestD990 : Fin 3 ->
    RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  ![Root0.tree, Root1.tree, Root2.tree]

theorem sectionSixP2Forest_valid_D990 (r : Fin 3) :
    (sectionSixP2ForestD990 r).coverValid sectionSixP2LeafValidD988
      (sectionSixP2RootD974 r) = true := by
  fin_cases r
  · exact Root0.valid
  · exact Root1.valid
  · exact Root2.valid

theorem sectionSixP2Forest_replay_D990 :
    (∑ r, (sectionSixP2ForestD990 r).replayWeightRat
      (sectionSixP2RootD974 r) (fun _ p => p.upper)) =
        (934501577370293699593907877 / 32768000000000000000000000000 : Rat) := by
  simp only [sectionSixP2ForestD990, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    show (0 : Fin 2).succ = (1 : Fin 3) from rfl,
    show (0 : Fin 1).succ.succ = (2 : Fin 3) from rfl]
  rw [Root0.replay, Root1.replay, Root2.replay]
  norm_num

theorem sectionSixP2Profile_integral_lt_D990 :
    (∫ x in {x : Fin 3 -> Real |
        ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter},
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2)) <
        (1427 / 50000 : Real) := by
  have hmeas : MeasurableSet {x : Fin 3 -> Real |
      ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter} := by
    unfold sectionSixFirstLowCentralSmallI5P2FullOuter
    measurability
  have h := sectionSixP2Forest_integral_le_D989 3 sectionSixP2RootD974
    sectionSixP2ForestD990 _ hmeas sectionSixP2FullOuter_subset_roots_D974
    sectionSixP2Forest_valid_D990
  rw [sectionSixP2Forest_replay_D990] at h
  apply h.trans_lt
  norm_num

end PrimesRestrictedDigits
