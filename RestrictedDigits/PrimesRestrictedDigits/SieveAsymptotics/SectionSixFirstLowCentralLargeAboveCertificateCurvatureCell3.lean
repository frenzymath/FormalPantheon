import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Data
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3SignedCertificate
import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
/-! Exact x-curvature certificate for the upper `I_4` cell 3. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
open SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
private noncomputable def cell3Specialize (p : BivariateRat) (y : Real) : Polynomial Real :=
  p.map (Polynomial.eval₂RingHom (algebraMap Rat Real) y)
private theorem cell3SignedCurvature_nonneg {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    0 ≤ (cell3Specialize cell3SignedCurvature y).eval x := by
  have h := tensorBernsteinPolynomial_eval₂_nonneg
    (n := 9) (m := 24) (coefficient := cell3BernsteinCoefficient)
    cell3BernsteinCoefficient_nonneg hy.1 hy.2 hx.1 hx.2
  change 0 ≤ Polynomial.eval₂
    (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell3Tensor at h
  rw [cell3Tensor_eq_power, ← cell3Signed_eq_power] at h
  simpa [cell3Specialize, Polynomial.eval₂_eq_eval_map] using h
private def cell3U (x : Real) : Real := 43 / 200 + (1 / 4 - 43 / 200) * x
private def cell3Ell (x : Real) : Real := 1 - 3 * cell3U x
private def cell3Low (x : Real) : Real := (212499 / 500000) * cell3Ell x
private def cell3Sn (x : Real) : Real :=
  2 * (287501 / 500000 - cell3U x) * cell3U x - cell3Low x
private def cell3N (x y : Real) : Real := cell3Low x + cell3Sn x * y
private def cell3D (x : Real) : Real := (212499 / 500000) * cell3U x
private def cell3Ph (x y : Real) : Real :=
  (-2 / 3) * cell3D x ^ 3 - 6 * cell3N x y * cell3D x ^ 2 + 6 * cell3N x y ^ 2 * cell3D x + (2 / 3) * cell3N x y ^ 3
private def cell3P (x y : Real) : Real := (1 / 4 - 43 / 200) * cell3Sn x * cell3Ph x y
private def cell3Q (x y : Real) : Real :=
  4 * (212499 / 500000) * cell3U x ^ 2 * (1 - cell3U x) * cell3N x y * (cell3N x y + cell3D x) ^ 2
private theorem cell3Polynomial_evaluation (x y : Real) :
    (cell3Specialize cell3RationalPolynomials.1 y).eval x = cell3P x y ∧
      (cell3Specialize cell3RationalPolynomials.2 y).eval x = cell3Q x y := by
  constructor
  · rw [cell3Specialize, cell3RationalPolynomials, cell3PFull, Polynomial.eval_map]
    unfold cell3PRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow,
      Finset.sum_range_succ]
    norm_num [cell3PScale, cell3PNumerator, cell3P, cell3Ph, cell3D,
      cell3N, cell3Sn, cell3Low, cell3Ell, cell3U, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Option.getD_none]
    ring_nf
  · rw [cell3Specialize, cell3RationalPolynomials, cell3QFull, Polynomial.eval_map]
    unfold cell3QRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow,
      Finset.sum_range_succ]
    norm_num [cell3QScale, cell3QNumerator, cell3Q, cell3D, cell3N,
      cell3Sn, cell3Low, cell3Ell, cell3U, List.getD_cons_zero, List.getD_cons_succ,
      List.getD_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none]
    ring_nf
private theorem cell3Factors_pos {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    0 < cell3U x ∧ 0 < cell3Ell x ∧ 0 < cell3Low x ∧ 0 < cell3Sn x ∧
      0 < cell3N x y ∧ 0 < cell3D x ∧ 0 < cell3N x y + cell3D x ∧
      0 < cell3Q x y := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have hu : 0 < cell3U x := by norm_num [cell3U]; linarith
  have huq : cell3U x ≤ 1 / 4 := by norm_num [cell3U]; linarith
  have homu : 0 < 1 - cell3U x := by linarith
  have hell : 0 < cell3Ell x := by norm_num [cell3Ell, cell3U]; linarith
  have hlow : 0 < cell3Low x := by unfold cell3Low; positivity
  have hsn : 0 < cell3Sn x := by
    norm_num [cell3Sn, cell3Low, cell3Ell, cell3U]
    nlinarith
  have hn : 0 < cell3N x y := by unfold cell3N; positivity
  have hd : 0 < cell3D x := by unfold cell3D; positivity
  have hnd : 0 < cell3N x y + cell3D x := add_pos hn hd
  have hq : 0 < cell3Q x y := by unfold cell3Q; positivity
  exact ⟨hu, hell, hlow, hsn, hn, hd, hnd, hq⟩
private noncomputable def cell3TightLog (r : Real) : Real := let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private noncomputable def cell3RLower (u : Real) : Real := (1 - u) / u - 2
private noncomputable def cell3RUpper (u : Real) : Real := (1 - u) / (212499 / 1000000) - 2
private noncomputable def cell3ChartR (x y : Real) : Real :=
  cell3RLower (cell3U x) + (cell3RUpper (cell3U x) - cell3RLower (cell3U x)) * y
private theorem cell3TightLog_eq_ratio {r : Real} (hr : 1 ≤ r) :
    cell3TightLog r = ((r - 1) * (r ^ 2 + 10 * r + 1)) /
      (6 * r * (r + 1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr1 : 0 < r + 1 := by linarith
  have hz : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by
    field_simp [hr1.ne']; ring
  dsimp [cell3TightLog]
  rw [hz]
  field_simp [hr0.ne', hr1.ne']; ring
private theorem cell3ChartR_eq_ratio {x y : Real} (hx : x ∈ Icc (0 : Real) 1) :
    cell3ChartR x y = cell3N x y / cell3D x := by
  have hu : 0 < cell3U x := by norm_num [cell3U] at hx ⊢; linarith
  dsimp [cell3ChartR, cell3RLower, cell3RUpper]
  unfold cell3N cell3D cell3Low cell3Sn cell3Ell
  field_simp [hu.ne']
  simp only [cell3Low, cell3Ell, cell3U]
  ring_nf
private theorem cell3ChartR_ge_one {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    1 ≤ cell3ChartR x y := by
  rw [cell3ChartR_eq_ratio hx]
  rcases cell3Factors_pos hx hy with ⟨hu, hell, hlow, hsn, hn, hd, hnd, hq⟩
  have huq : cell3U x ≤ 1 / 4 := by norm_num [cell3U] at hx ⊢; linarith
  have hdn : cell3D x ≤ cell3N x y := by
    have hdlow : cell3D x ≤ cell3Low x := by
      unfold cell3D cell3Low cell3Ell
      simp only [cell3U]
      norm_num
      nlinarith [hx.2]
    exact hdlow.trans (le_add_of_nonneg_right (mul_nonneg hsn.le hy.1))
  exact (le_div_iff₀ hd).2 (by simpa only [one_mul] using hdn)
private theorem cell3Transformed_expansion {x y : Real}
    (_hx : x ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
      cell3TightLog (3 : Fin 5) x y =
      (1 / 4 - 43 / 200) *
        (cell3RUpper (cell3U x) - cell3RLower (cell3U x)) *
          (cell3TightLog (cell3ChartR x y) /
            (cell3U x * (1 - cell3U x) * (cell3ChartR x y + 1))) := by
  have hlow :
      (1 - cell3U x) / cell3U x - 2 = cell3RLower (cell3U x) := by
    dsimp [cell3RLower]
  have hupper :
      (1 - cell3U x) / ((212499 / 500000 : Real) / 2) - 2 =
        cell3RUpper (cell3U x) := by
    dsimp [cell3RUpper]
    norm_num
  change (1 / 4 - 43 / 200) *
    (((1 - cell3U x) / ((212499 / 500000) / 2) - 2) -
      ((1 - cell3U x) / cell3U x - 2)) *
      (cell3TightLog
        ((1 - cell3U x) / cell3U x - 2 +
          (((1 - cell3U x) / ((212499 / 500000) / 2) - 2) -
            ((1 - cell3U x) / cell3U x - 2)) * y) /
        (cell3U x * (1 - cell3U x) *
          ((1 - cell3U x) / cell3U x - 2 +
            (((1 - cell3U x) / ((212499 / 500000) / 2) - 2) -
              ((1 - cell3U x) / cell3U x - 2)) * y + 1))) = _
  rw [hlow, hupper, cell3ChartR]
private theorem cell3Transformed_eq_quotient {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
      cell3TightLog (3 : Fin 5) x y = cell3P x y / cell3Q x y := by
  rcases cell3Factors_pos hx hy with ⟨hu, hell, hlow, hsn, hn, hd, hnd, hq⟩
  have homu : 0 < 1 - cell3U x := by
    norm_num [cell3U]
    nlinarith [hx.2]
  let r := cell3N x y / cell3D x
  have hr : 0 < r := div_pos hn hd
  have hrc : cell3ChartR x y = r := cell3ChartR_eq_ratio hx
  have hrOne : 1 ≤ r := by
    rw [← hrc]; exact cell3ChartR_ge_one hx hy
  have hspan : cell3RUpper (cell3U x) - cell3RLower (cell3U x) =
      cell3Sn x / cell3D x := by
    dsimp [cell3RUpper, cell3RLower, cell3D, cell3Sn, cell3Low, cell3Ell]
    field_simp [hu.ne']; ring
  have hone : r + 1 = (cell3N x y + cell3D x) / cell3D x := by
    dsimp [r]; field_simp [hd.ne']
  have hlog : cell3TightLog r = cell3Ph x y /
      (4 * cell3D x * cell3N x y * (cell3N x y + cell3D x)) := by
    rw [cell3TightLog_eq_ratio hrOne]
    dsimp [r]
    unfold cell3Ph
    field_simp [hn.ne', hd.ne', hnd.ne']; ring
  rw [cell3Transformed_expansion hx, hrc, hspan, hlog, hone]
  field_simp [hu.ne', homu.ne', hn.ne', hd.ne', hnd.ne', hq.ne']
  unfold cell3P cell3Q cell3D
  ring
private noncomputable def cell3QuotientNegativeSecondNumerator
    (p q : Polynomial Real) (x : Real) : Real :=
  -(p.derivative.derivative.eval x * q.eval x ^ 2 -
    2 * p.derivative.eval x * q.eval x * q.derivative.eval x +
    2 * p.eval x * q.derivative.eval x ^ 2 -
    p.eval x * q.eval x * q.derivative.derivative.eval x)
private theorem cell3SignedCurvature_evaluation (x y : Real) :
    (cell3Specialize cell3SignedCurvature y).eval x =
      cell3QuotientNegativeSecondNumerator
        (cell3Specialize cell3RationalPolynomials.1 y)
        (cell3Specialize cell3RationalPolynomials.2 y) x := by
  simp [cell3Specialize, cell3SignedCurvature, cell3Constant,
    cell3QuotientNegativeSecondNumerator, Polynomial.derivative_map]
private theorem cell3ConcaveOn_polynomial_quotient
    (p q : Polynomial Real)
    (hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x)
    (hsigned : ∀ x ∈ Icc (0 : Real) 1,
      0 ≤ cell3QuotientNegativeSecondNumerator p q x) :
    ConcaveOn Real (Icc (0 : Real) 1) (fun x => p.eval x / q.eval x) := by
  let f1 : Real → Real := fun x =>
    (p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2
  let f2 : Real → Real := fun x =>
    -cell3QuotientNegativeSecondNumerator p q x / q.eval x ^ 3
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
    (convex_Icc (0 : Real) 1)
  · intro x hx
    exact ((Polynomial.hasDerivAt p x).continuousAt.div
      (Polynomial.hasDerivAt q x).continuousAt (hq x hx).ne').continuousWithinAt
  · intro x hx
    have hm := interior_subset hx
    exact (((Polynomial.hasDerivAt p x).div (Polynomial.hasDerivAt q x)
      (hq x hm).ne').congr_deriv (by dsimp [f1])).hasDerivWithinAt
  · intro x hx
    have hm := interior_subset hx
    have hqx := hq x hm
    have hp := Polynomial.hasDerivAt p x
    have hpd := Polynomial.hasDerivAt p.derivative x
    have hq0 := Polynomial.hasDerivAt q x
    have hqd := Polynomial.hasDerivAt q.derivative x
    have hnum := (hpd.mul hq0).sub (hp.mul hqd)
    have hden := hq0.pow 2
    exact (hnum.div hden (pow_ne_zero 2 hqx.ne')).congr_deriv (by
      dsimp [f1, f2, cell3QuotientNegativeSecondNumerator]
      field_simp [hqx.ne']; ring) |>.hasDerivWithinAt
  · intro x hx
    have hm := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hsigned x hm))
      (pow_nonneg (hq x hm).le 3)
theorem sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell3
    (y : Real) (hy : y ∈ Icc (0 : Real) 1) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ConcaveOn Real (Icc (0 : Real) 1)
      (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        tightLog (3 : Fin 5) x y) := by
  dsimp only
  let p := cell3Specialize cell3RationalPolynomials.1 y
  let q := cell3Specialize cell3RationalPolynomials.2 y
  have heval (x : Real) := cell3Polynomial_evaluation x y
  have hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x := by
    intro x hx
    dsimp [q]
    rw [(heval x).2]
    exact (cell3Factors_pos hx hy).2.2.2.2.2.2.2
  have hsigned : ∀ x ∈ Icc (0 : Real) 1,
      0 ≤ cell3QuotientNegativeSecondNumerator p q x := by
    intro x hx
    dsimp [p, q]
    rw [← cell3SignedCurvature_evaluation]
    exact cell3SignedCurvature_nonneg hx hy
  refine (cell3ConcaveOn_polynomial_quotient p q hq hsigned).congr ?_
  intro x hx
  dsimp [p, q]
  rw [(heval x).1, (heval x).2]
  exact (cell3Transformed_eq_quotient hx hy).symm
end
end PrimesRestrictedDigits
