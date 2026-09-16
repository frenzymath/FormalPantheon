import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
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
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1Data
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TensorCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCertificate
/-! Exact x-curvature certificate for the upper `I_4` cell 1. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
open SectionSixFirstLowCentralLargeAboveCell1Certificate
private noncomputable def cell1Specialize
    (p : BivariateRat) (y : Real) : Polynomial Real :=
  p.map (Polynomial.eval₂RingHom (algebraMap Rat Real) y)
private theorem cell1SignedCurvature_nonneg {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    0 ≤ (cell1Specialize cell1SignedCurvature y).eval x := by
  have h := tensorBernsteinPolynomial_eval₂_nonneg
    (n := 10) (m := 12) (coefficient := cell1BernsteinCoefficient)
    cell1BernsteinCoefficient_nonneg hy.1 hy.2 hx.1 hx.2
  change 0 ≤ Polynomial.eval₂
    (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell1Tensor at h
  rw [cell1Tensor_eq_power] at h
  rw [cell1Signed_eq_y_mul_power]
  simpa [cell1Specialize, Polynomial.eval₂_eq_eval_map] using mul_nonneg hy.1 h
private def cell1U (x : Real) : Real :=
  470003 / 1500000 + (180001 / 500000 - 470003 / 1500000) * x
private def cell1Span (x : Real) : Real :=
  2 * (287501 / 500000 - cell1U x) - 212499 / 500000
private def cell1N (x y : Real) : Real :=
  212499 / 500000 + cell1Span x * y
private def cell1A (x y : Real) : Real :=
  cell1U x - 287501 / 500000 + cell1N x y
private def cell1Ph (x y : Real) : Real :=
  (-2 / 3) * (212499 / 500000 : Real) ^ 3 -
    6 * cell1N x y * (212499 / 500000 : Real) ^ 2 +
    6 * cell1N x y ^ 2 * (212499 / 500000 : Real) +
    (2 / 3) * cell1N x y ^ 3
private def cell1P (x y : Real) : Real :=
  (180001 / 500000 - 470003 / 1500000) * cell1Span x * cell1Ph x y
private def cell1Q (x y : Real) : Real :=
  4 * (212499 / 500000 : Real) * cell1U x * cell1N x y *
    (cell1N x y + 212499 / 500000) ^ 2 * cell1A x y
private theorem cell1Polynomial_evaluation (x y : Real) :
    (cell1Specialize cell1RationalPolynomials.1 y).eval x = cell1P x y ∧
      (cell1Specialize cell1RationalPolynomials.2 y).eval x = cell1Q x y := by
  constructor
  · rw [cell1Specialize, cell1RationalPolynomials, cell1PFull, Polynomial.eval_map]; unfold cell1PRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow, Finset.sum_range_succ]
    norm_num [cell1PScale, cell1PNumerator, cell1P, cell1Ph, cell1N, cell1Span,
      cell1U, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Option.getD_none]; ring_nf
  · rw [cell1Specialize, cell1RationalPolynomials, cell1QFull, Polynomial.eval_map]; unfold cell1QRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow, Finset.sum_range_succ]
    norm_num [cell1QScale, cell1QNumerator, cell1Q, cell1A, cell1N, cell1Span,
      cell1U, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Option.getD_none]; ring_nf
private theorem cell1Factors_pos {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    0 < cell1U x ∧ 0 < cell1Span x ∧ 0 < cell1N x y ∧
      0 < cell1N x y + 212499 / 500000 ∧ 0 < cell1A x y ∧
      0 < cell1Q x y := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have hu : 0 < cell1U x := by norm_num [cell1U]; linarith
  have hs : 0 < cell1Span x := by norm_num [cell1Span, cell1U]; linarith
  have hn : 0 < cell1N x y := by unfold cell1N; positivity
  have hnb : 0 < cell1N x y + 212499 / 500000 := by positivity
  have ha : 0 < cell1A x y := by
    norm_num [cell1A, cell1N, cell1Span, cell1U] at *; nlinarith
  have hq : 0 < cell1Q x y := by unfold cell1Q; positivity
  exact ⟨hu, hs, hn, hnb, ha, hq⟩
private noncomputable def cell1TightLog (r : Real) : Real :=
  let z := (r - 1) / (r + 1)
  2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private def cell1RLower (u : Real) : Real :=
  (287501 / 500000 - u) /
    (212499 / 500000 - (u - 37501 / 250000))
private def cell1RUpper (u : Real) : Real :=
  (287501 / 500000 - u) /
    (212499 / 500000 - (212499 / 500000) / 2)
private def cell1ChartR (x y : Real) : Real :=
  cell1RLower (cell1U x) +
    (cell1RUpper (cell1U x) - cell1RLower (cell1U x)) * y
private theorem cell1TightLog_eq_ratio {r : Real} (hr : 1 ≤ r) :
    cell1TightLog r = ((r - 1) * (r ^ 2 + 10 * r + 1)) /
      (6 * r * (r + 1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr1 : 0 < r + 1 := by linarith
  have hz : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by
    field_simp [hr1.ne']; ring
  dsimp [cell1TightLog]; rw [hz]
  field_simp [hr0.ne', hr1.ne']; ring
private theorem cell1RLower_eq_one {u : Real}
    (hu : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000)) :
    cell1RLower u = 1 := by
  have h : 0 < (287501 / 500000 : Real) - u := by
    norm_num at hu ⊢; linarith
  dsimp [cell1RLower]
  have hd : (212499 / 500000 : Real) - (u - 37501 / 250000) =
      287501 / 500000 - u := by ring
  rw [hd, div_self h.ne']
private theorem cell1RUpper_eq {u : Real} :
    cell1RUpper u = 2 * (287501 / 500000 - u) / (212499 / 500000) := by
  dsimp [cell1RUpper]; norm_num; ring
private theorem cell1ChartR_eq_ratio {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) :
    cell1ChartR x y = cell1N x y / (212499 / 500000 : Real) := by
  have hu : cell1U x ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) := by
    norm_num [cell1U] at hx ⊢; constructor <;> nlinarith
  rw [cell1ChartR, cell1RLower_eq_one hu, cell1RUpper_eq]
  dsimp [cell1N, cell1Span]
  field_simp
private theorem cell1ChartR_ge_one {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    1 ≤ cell1ChartR x y := by
  rw [cell1ChartR_eq_ratio hx]
  have hs : 0 < cell1Span x := by
    norm_num [cell1Span, cell1U] at hx ⊢; linarith
  have hn : (212499 / 500000 : Real) <= cell1N x y := by
    unfold cell1N
    exact le_add_of_nonneg_right (mul_nonneg hs.le hy.1)
  exact (le_div_iff₀ (by norm_num)).2 (by simpa using hn)
private theorem cell1Transformed_eq_quotient {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
      cell1TightLog (1 : Fin 5) x y = cell1P x y / cell1Q x y := by
  rcases cell1Factors_pos hx hy with ⟨hu0, hs, hn, hnb, ha, hq⟩
  have hu : cell1U x ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) := by
    norm_num [cell1U] at hx ⊢; constructor <;> nlinarith
  have hru := cell1RLower_eq_one hu
  let r : Real := cell1N x y / (212499 / 500000)
  have hrpos : 0 < r := div_pos hn (by norm_num)
  have hrc : cell1ChartR x y = r := cell1ChartR_eq_ratio hx
  have hrOne : 1 ≤ r := by rw [← hrc]; exact cell1ChartR_ge_one hx hy
  have hspan : cell1RUpper (cell1U x) - cell1RLower (cell1U x) =
      cell1Span x / (212499 / 500000 : Real) := by
    rw [hru, cell1RUpper_eq]; unfold cell1Span; field_simp
  have hone : r + 1 =
      (cell1N x y + 212499 / 500000) / (212499 / 500000 : Real) := by
    dsimp [r]; field_simp
  have hlast : cell1U x + (212499 / 500000) * r - 287501 / 500000 =
      cell1A x y := by
    dsimp [r]; unfold cell1A; field_simp; ring
  have hlog : cell1TightLog r =
      cell1Ph x y /
        (4 * (212499 / 500000) * cell1N x y *
          (cell1N x y + 212499 / 500000)) := by
    rw [cell1TightLog_eq_ratio hrOne]
    dsimp [r]; unfold cell1Ph
    field_simp [hrpos.ne', hn.ne', hnb.ne']; ring
  change (180001 / 500000 - 470003 / 1500000) *
    (cell1RUpper (cell1U x) - cell1RLower (cell1U x)) *
      (cell1TightLog (cell1ChartR x y) /
        (cell1U x * (cell1ChartR x y + 1) *
          (cell1U x + (212499 / 500000) * cell1ChartR x y -
            287501 / 500000))) = cell1P x y / cell1Q x y
  rw [hrc, hspan, hlog, hone, hlast]
  field_simp [hu0.ne', hn.ne', hnb.ne', ha.ne', hq.ne']
  unfold cell1P cell1Q; ring
private noncomputable def cell1QuotientSecondNumerator
    (p q : Polynomial Real) (x : Real) : Real :=
  p.derivative.derivative.eval x * q.eval x ^ 2 -
    2 * p.derivative.eval x * q.eval x * q.derivative.eval x +
    2 * p.eval x * q.derivative.eval x ^ 2 -
    p.eval x * q.eval x * q.derivative.derivative.eval x
private theorem cell1SignedCurvature_evaluation (x y : Real) :
    (cell1Specialize cell1SignedCurvature y).eval x =
      cell1QuotientSecondNumerator
        (cell1Specialize cell1RationalPolynomials.1 y)
        (cell1Specialize cell1RationalPolynomials.2 y) x := by
  simp [cell1Specialize, cell1SignedCurvature, cell1Constant,
    cell1QuotientSecondNumerator, Polynomial.derivative_map, Polynomial.C_ofNat]
private theorem cell1Quotient_convexOn (p q : Polynomial Real)
    (hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x)
    (hn : ∀ x ∈ Icc (0 : Real) 1,
      0 ≤ cell1QuotientSecondNumerator p q x) :
    ConvexOn Real (Icc (0 : Real) 1) (fun x => p.eval x / q.eval x) := by
  let f1 := fun x : Real => (p.derivative.eval x * q.eval x -
    p.eval x * q.derivative.eval x) / q.eval x ^ 2
  let f2 := fun x : Real => cell1QuotientSecondNumerator p q x / q.eval x ^ 3
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f1) (f'' := f2)
    (convex_Icc (0 : Real) 1)
  · intro x hx
    exact ((Polynomial.hasDerivAt p x).continuousAt.div
      (Polynomial.hasDerivAt q x).continuousAt (hq x hx).ne').continuousWithinAt
  · intro x hx
    exact (((Polynomial.hasDerivAt p x).div (Polynomial.hasDerivAt q x)
      (hq x (interior_subset hx)).ne').congr_deriv (by dsimp [f1])).hasDerivWithinAt
  · intro x hx
    have hqx := hq x (interior_subset hx)
    have hp := Polynomial.hasDerivAt p x
    have hpd := Polynomial.hasDerivAt p.derivative x
    have hq0 := Polynomial.hasDerivAt q x
    have hqd := Polynomial.hasDerivAt q.derivative x
    exact (((hpd.mul hq0).sub (hp.mul hqd)).div (hq0.pow 2)
      (pow_ne_zero 2 hqx.ne')).congr_deriv (by
        dsimp [f1, f2, cell1QuotientSecondNumerator]
        field_simp [hqx.ne']; ring) |>.hasDerivWithinAt
  · intro x hx
    exact div_nonneg (hn x (interior_subset hx))
      (pow_nonneg (hq x (interior_subset hx)).le 3)
theorem sectionSixFirstLowCentralLargeAbove_tight_convexOn_x_cell1
    (y : Real) (hy : y ∈ Icc (0 : Real) 1) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ConvexOn Real (Icc (0 : Real) 1)
      (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        tightLog (1 : Fin 5) x y) := by
  dsimp only
  let p := cell1Specialize cell1RationalPolynomials.1 y
  let q := cell1Specialize cell1RationalPolynomials.2 y
  have heval (x : Real) := cell1Polynomial_evaluation x y
  have hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x := by
    intro x hx; dsimp [q]; rw [(heval x).2]
    exact (cell1Factors_pos hx hy).2.2.2.2.2
  have hsigned : ∀ x ∈ Icc (0 : Real) 1,
      0 ≤ cell1QuotientSecondNumerator p q x := by
    intro x hx; dsimp [p, q]; rw [← cell1SignedCurvature_evaluation]
    exact cell1SignedCurvature_nonneg hx hy
  refine (cell1Quotient_convexOn p q hq hsigned).congr ?_
  intro x hx; dsimp [p, q]; rw [(heval x).1, (heval x).2]
  exact (cell1Transformed_eq_quotient hx hy).symm
end
end PrimesRestrictedDigits
