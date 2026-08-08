import Waring.Analytic.ChenSevenResidueIndex
import Waring.Analytic.ChenSevenResidueIntegral

/-!
# The large-modulus branch of Chen's residue approximation

When `P < q`, a residue class contains at most one integer in `1, ..., P`.
This closes the part of the uniform residue interface that lies outside
Chen's small-denominator application.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- For `P < q`, one residue class contributes at most one unit-modulus
summand. -/
theorem norm_residueFifthPerturbationSum_le_one_of_lt
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q)
    (hPq : P < q) :
    ‖residueFifthPerturbationSum q z P y‖ ≤ 1 := by
  let r := positiveResidueRepresentative q y
  by_cases hrP : r ≤ P
  · have hdiff : P - r < q := (Nat.sub_le P r).trans_lt hPq
    have hdiv : (P - r) / q = 0 := Nat.div_eq_of_lt hdiff
    rw [residueFifthPerturbationSum_eq_sum_range q z P y hrP]
    change ‖∑ k ∈ Finset.range ((P - r) / q + 1),
      Complex.exp
        (Complex.I * fifthPerturbationPhase z (r + q * k) 0)‖ ≤ 1
    rw [hdiv]
    simp [Complex.norm_exp_I_mul_ofReal]
  · have hPr : P < r := Nat.lt_of_not_ge hrP
    rw [residueFifthPerturbationSum_eq_zero_of_lt q z P y hPr]
    norm_num

/-- The one-class approximation has the stronger error `2` when `P < q`. -/
theorem norm_residueFifthPerturbationSum_sub_mainTerm_le_two_of_lt
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q)
    (hPq : P < q) :
    ‖residueFifthPerturbationSum q z P y -
        (q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ ≤ 2 := by
  have hsum := norm_residueFifthPerturbationSum_le_one_of_lt
    q z P y hPq
  have hqNat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : Real) < q := by exact_mod_cast hqNat
  have hPqReal : (P : Real) < q := by exact_mod_cast hPq
  have hmain :
      ‖(q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ ≤ 1 := by
    calc
      ‖(q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ =
          (q : Real)⁻¹ * ‖fifthPerturbationIntegral z P‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (q : Real)⁻¹ * P := by
        gcongr
        exact norm_fifthPerturbationIntegral_le z P
      _ ≤ 1 := by
        rw [inv_mul_eq_div]
        exact (div_le_one hq).2 hPqReal.le
  calc
    ‖residueFifthPerturbationSum q z P y -
        (q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ ≤
        ‖residueFifthPerturbationSum q z P y‖ +
          ‖(q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hsum hmain
    _ = 2 := by norm_num

end Waring.Analytic
