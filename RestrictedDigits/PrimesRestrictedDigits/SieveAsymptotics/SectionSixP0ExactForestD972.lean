import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Root0
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Root1
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P0ForestD972.Root2

/-!
# Exact forest certificate for the P0 two-ceiling profile

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). All leaf data, root paths and replay
sums are checked in the imported shards.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

open SectionSixP0CertificateD972

def sectionSixP0ForestD972 : Fin 3 -> RationalTetraSubdivision Rat :=
  ![Root0.tree, Root1.tree, Root2.tree]

theorem sectionSixP0Forest_valid_D972 (r : Fin 3) :
    (sectionSixP0ForestD972 r).coverValid sectionSixP0LeafValidD970
      (sectionSixP0RootD971 r) = true := by
  fin_cases r
  · exact Root0.valid
  · exact Root1.valid
  · exact Root2.valid

theorem sectionSixP0Forest_replay_D972 :
    (∑ r, (sectionSixP0ForestD972 r).replayWeightRat
      (sectionSixP0RootD971 r) (fun _ q => q)) =
        (139647848921862518270854511 / 6144000000000000000000000000 : Rat) := by
  simp only [sectionSixP0ForestD972, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    show (0 : Fin 2).succ = (1 : Fin 3) from rfl,
    show (0 : Fin 1).succ.succ = (2 : Fin 3) from rfl]
  rw [Root0.replay, Root1.replay, Root2.replay]
  norm_num

theorem sectionSixP0Profile_integral_lt_D972 :
    (∫ x in {x : Fin 3 -> Real |
        ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase},
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2)) <
        (2273 / 100000 : Real) := by
  have hmeas : MeasurableSet {x : Fin 3 -> Real |
      ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase} := by
    exact IsClosed.measurableSet (IsClosed.preimage (by fun_prop)
      sectionSixFirstLowCentralSmallI5P0RefinedBase_isCompact.isClosed)
  have h := sectionSixP0Forest_integral_le_D970 3 sectionSixP0RootD971
    sectionSixP0ForestD972 _ hmeas sectionSixP0Base_subset_roots_D971
    sectionSixP0Forest_valid_D972
  rw [sectionSixP0Forest_replay_D972] at h
  apply h.trans_lt
  norm_num

end PrimesRestrictedDigits
