import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import PrimesRestrictedDigits.BasicEstimates.PrimeProductBounds
import PrimesRestrictedDigits.TypeI.PropositionSevenOne
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite and Type-I bridges for the source aggregate

These are implementation bridges for the corrected source split, kept separate from the scalar
aggregate proof.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sourceFundamental_toPNat'_coe_of_mem
    {Y y : Real} {d : Nat}
    (hd : d ∈ maynardStrictRoughCarrier Y y) :
    ((d.toPNat' : PNat) : Nat) = d := by
  have hdData := mem_maynardStrictRoughCarrier.mp hd
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdData.1
  rw [Nat.toPNat'_coe, if_pos hd0]

theorem sourceFundamental_typeI_sum_normalized
    {length0 length : Nat} (hLength : length0 ≤ length)
    (digit : Fin 10) (Q : Real)
    (hQ : Q <= (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
      Real.log (((10 ^ length : Nat) : Real)) ^ (-2 * (100 : Real) - 2))
    (hEstimate : ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
      Q <= (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
        Real.log (((10 ^ length : Nat) : Real)) ^ (-2 * (100 : Real) - 2) →
      (∑ q ∈ typeIModuliBelow Q,
        |(((paddedRestrictedNumbers digit length).filter
            (fun n => q ∣ n ∧ n.Coprime 10)).card : Real) -
          (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (q : Real)|) <=
        4 * (26400 * largeSieveConstant + 720) *
          ((paddedRestrictedNumbers digit length).card : Real) *
            Real.log (((10 ^ length : Nat) : Real)) ^ (-100 : Real)) :
    (∑ q ∈ typeIModuliBelow Q,
      |realTypeIProgressionError digit length q|) <=
      4 * (26400 * largeSieveConstant + 720) *
        ((paddedRestrictedNumbers digit length).card : Real) *
          Real.log (((10 ^ length : Nat) : Real)) ^ (-100 : Real) := by
  have h := hEstimate length hLength digit Q hQ
  simpa [realTypeIProgressionError] using h

theorem sourceFundamental_typeIProgressionDensity_bounds (digit : Fin 10) :
    0 <= (typeIProgressionDensity digit : Real) ∧
      (typeIProgressionDensity digit : Real) <= 1 := by
  rw [typeIProgressionDensity_eq]
  split_ifs <;> norm_num

theorem sourceFundamental_decimalExcludedPrimeProduct_nonneg
    {z : Real} (_hz : 5 <= z) :
    0 <= decimalExcludedPrimeProduct z := by
  rw [decimalExcludedPrimeProduct]
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
  exact (sub_nonneg.mpr (inv_le_one_of_one_le₀ hpOne.le))

theorem sourceFundamental_decimalExcludedPrimeProduct_mul_inv_le
    {X delta : Real} (hX : 1 < X) (hdelta : 0 < delta)
    (hcutoff : 5 <= X ^ delta) :
    decimalExcludedPrimeProduct (X ^ delta) <=
      5 / (2 * delta * Real.log X) :=
  decimalExcludedPrimeProduct_rpow_le hX hdelta hcutoff

end

end PrimesRestrictedDigits
