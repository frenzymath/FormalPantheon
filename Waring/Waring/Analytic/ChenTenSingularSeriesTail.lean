import Waring.Analytic.ChenTenSingularSeries
import Mathlib.Analysis.PSeries

/-!
# A quantitative tail bound for Chen's singular series

Quadratic decay of the finite coefficients gives a uniform truncation error
[CHEN1964-EN, p. 1563, equation (34); CHEN1964-ZH, p. 729].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The singular series truncated after all positive moduli through `Q`.
The zero-modulus term is included but is definitionally zero. -/
noncomputable def chenTenSingularSeriesPartial (n Q : Nat) : Complex :=
  ∑ q ∈ Finset.range (Q + 1), chenTenSingularCoefficientNat n q

/-- A shifted inverse-square series has the coarse explicit tail bound used
for the singular-series truncation. -/
theorem tsum_shifted_inv_sq_le (Q : Nat) :
    (∑' k : Nat, ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹)) <=
      2 / (Q + 1 : Real) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    positivity
  · intro m
    have h := sum_Ioo_inv_sq_le (α := Real) Q (Q + m + 1)
    rw [← Finset.Ico_succ_left_eq_Ioo,
      Finset.sum_Ico_eq_sum_range] at h
    have hdiff : Q + (m + 1) - (Q + 1) = m := by omega
    simpa [hdiff, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Chen's singular series differs from its truncation through `Q` by at
most the explicit quadratic-decay tail. -/
theorem norm_chenTenSingularSeries_sub_partial_le (n Q : Nat) :
    ‖chenTenSingularSeries n - chenTenSingularSeriesPartial n Q‖ <=
      2 * (40 : Real) ^ 15 / (Q + 1 : Real) := by
  let f : Nat -> Complex := chenTenSingularCoefficientNat n
  have hf : Summable f := summable_chenTenSingularCoefficientNat n
  have hsplit :
      (∑ q ∈ Finset.range (Q + 1), f q) +
          ∑' k : Nat, f (k + (Q + 1)) =
        ∑' q : Nat, f q :=
    hf.sum_add_tsum_nat_add (Q + 1)
  have htail :
      chenTenSingularSeries n - chenTenSingularSeriesPartial n Q =
        ∑' k : Nat, f (k + Q + 1) := by
    unfold chenTenSingularSeries chenTenSingularSeriesPartial
    change (∑' q : Nat, f q) - (∑ q ∈ Finset.range (Q + 1), f q) = _
    rw [← hsplit]
    simp only [Nat.add_assoc]
    ring
  rw [htail]
  have hnorm : Summable (fun k : Nat => ‖f (k + Q + 1)‖) := by
    simpa only [Nat.add_assoc] using
      ((summable_nat_add_iff (Q + 1)).2 hf.norm)
  have hinv0 : Summable (fun q : Nat => (((q : Real) ^ 2)⁻¹)) := by
    exact Real.summable_nat_pow_inv.mpr (by norm_num)
  have hinv :
      Summable (fun k : Nat =>
        ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹)) := by
    simpa only [Nat.add_assoc] using
      ((summable_nat_add_iff (Q + 1)).2 hinv0)
  have hmajor :
      Summable (fun k : Nat =>
        (40 : Real) ^ 15 *
          ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹)) :=
    hinv.mul_left ((40 : Real) ^ 15)
  calc
    ‖∑' k : Nat, f (k + Q + 1)‖ <=
        ∑' k : Nat, ‖f (k + Q + 1)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ <= ∑' k : Nat,
        (40 : Real) ^ 15 *
          ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹) := by
      apply hnorm.tsum_le_tsum
      · intro k
        have h := norm_chenTenSingularCoefficientNat_le n (k + Q + 1)
        have hpos : (0 : Real) < (k + Q + 1 : Nat) := by positivity
        have hpow :
            ((k + Q + 1 : Nat) : Real) ^ (-2 : Real) =
              ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹) := by
          rw [show (-2 : Real) = -(2 : Nat) by norm_num,
            Real.rpow_neg_natCast]
          norm_num
          rfl
        calc
          ‖f (k + Q + 1)‖ <=
              (40 : Real) ^ 15 *
                ((k + Q + 1 : Nat) : Real) ^ (-2 : Real) := h
          _ = (40 : Real) ^ 15 *
              ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹) := by rw [hpow]
      · exact hmajor
    _ = (40 : Real) ^ 15 *
        (∑' k : Nat, ((((k + Q + 1 : Nat) : Real) ^ 2)⁻¹)) := by
      rw [tsum_mul_left]
    _ <= (40 : Real) ^ 15 * (2 / (Q + 1 : Real)) := by
      gcongr
      exact tsum_shifted_inv_sq_le Q
    _ = 2 * (40 : Real) ^ 15 / (Q + 1 : Real) := by ring

end Waring.Analytic
