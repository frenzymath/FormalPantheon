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
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2SignedCertificate
/-! Exact x-curvature certificate for the upper `I_4` cell 2. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
open SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
private noncomputable def cell2Specialize (p : BivariateRat) (y : Real) : Polynomial Real := p.map (Polynomial.eval₂RingHom (algebraMap Rat Real) y)
private theorem cell2SignedCurvature_nonneg {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 ≤ (cell2Specialize cell2SignedCurvature y).eval x := by have h := tensorBernsteinPolynomial_eval₂_nonneg (n := 9) (m := 26) (coefficient := cell2BernsteinCoefficient) cell2BernsteinCoefficient_nonneg hy.1 hy.2 hx.1 hx.2; change 0 ≤ Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell2Tensor at h; rw [cell2Tensor_eq_power, ← cell2Signed_eq_power] at h; simpa [cell2Specialize, Polynomial.eval₂_eq_eval_map] using h
private noncomputable def cell2U (x : Real) : Real := 319999 / 1500000 + (43 / 200 - 319999 / 1500000) * x
private noncomputable def cell2Ell (x : Real) : Real := 1 - 3 * cell2U x
private noncomputable def cell2E (x : Real) : Real := 319999 / 500000 - cell2U x
private noncomputable def cell2Low (x : Real) : Real := cell2Ell x * cell2E x
private noncomputable def cell2Sn (x : Real) : Real := (180001 / 250000) * cell2U x - cell2Low x
private noncomputable def cell2N (x y : Real) : Real := cell2Low x + cell2Sn x * y
private noncomputable def cell2D (x : Real) : Real := cell2U x * cell2E x
private noncomputable def cell2Ph (x y : Real) : Real := (-2 / 3) * cell2D x ^ 3 - 6 * cell2N x y * cell2D x ^ 2 + 6 * cell2N x y ^ 2 * cell2D x + (2 / 3) * cell2N x y ^ 3
private noncomputable def cell2P (x y : Real) : Real := (2501 / 1500000) * cell2Sn x * cell2Ph x y
private noncomputable def cell2Q (x y : Real) : Real := 4 * cell2U x ^ 2 * cell2E x * (1 - cell2U x) * cell2N x y * (cell2N x y + cell2D x) ^ 2
private theorem cell2Polynomial_evaluation (x y : Real) : (cell2Specialize cell2RationalPolynomials.1 y).eval x = cell2P x y ∧ (cell2Specialize cell2RationalPolynomials.2 y).eval x = cell2Q x y := by
  constructor
  · rw [cell2Specialize, cell2RationalPolynomials, cell2PFull, Polynomial.eval_map]
    unfold cell2PRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow]
    simp_rw [Finset.sum_range_succ]
    norm_num [cell2PScale, cell2PNumerator, cell2P, cell2Ph, cell2D,
      cell2N, cell2Sn, cell2Low, cell2E, cell2Ell, cell2U,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Option.getD_none]; ring_nf
  · rw [cell2Specialize, cell2RationalPolynomials, cell2QFull, Polynomial.eval_map]
    unfold cell2QRow
    simp_rw [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow]
    simp_rw [Finset.sum_range_succ]
    norm_num [cell2QScale, cell2QNumerator, cell2Q, cell2D, cell2N,
      cell2Sn, cell2Low, cell2E, cell2Ell, cell2U,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Option.getD_none]; ring_nf
private theorem cell2Factors_pos {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 < cell2U x ∧ 0 < cell2Ell x ∧ 0 < cell2E x ∧ 0 ≤ cell2Sn x ∧ 0 < cell2Low x ∧ 0 < cell2N x y ∧ 0 < cell2D x ∧ 0 < cell2N x y + cell2D x ∧ 0 < cell2Q x y := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have hu : 0 < cell2U x := by norm_num [cell2U]; linarith
  have huq : cell2U x < 1 := by norm_num [cell2U]; linarith
  have hell : 0 < cell2Ell x := by norm_num [cell2Ell, cell2U]; linarith
  have he : 0 < cell2E x := by norm_num [cell2E, cell2U]; linarith
  have hlow : 0 < cell2Low x := by unfold cell2Low; positivity
  have hsn : 0 ≤ cell2Sn x := by norm_num [cell2Sn, cell2Low, cell2Ell, cell2E, cell2U]; nlinarith
  have hn : 0 < cell2N x y := by unfold cell2N; exact add_pos_of_pos_of_nonneg hlow (mul_nonneg hsn hy0)
  have hd : 0 < cell2D x := by unfold cell2D; positivity
  have hnd : 0 < cell2N x y + cell2D x := by positivity
  have hq : 0 < cell2Q x y := by unfold cell2Q; positivity
  exact ⟨hu, hell, he, hsn, hlow, hn, hd, hnd, hq⟩
private noncomputable def cell2TightLog (r : Real) : Real := let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private noncomputable def cell2RLower (u : Real) : Real := (1 - u) / u - 2
private noncomputable def cell2RUpper (u : Real) : Real := (1 - u) / ((319999 / 500000 - u) / 2) - 2
private noncomputable def cell2ChartR (x y : Real) : Real := cell2RLower (cell2U x) + (cell2RUpper (cell2U x) - cell2RLower (cell2U x)) * y
private theorem cell2TightLog_eq_ratio {r : Real} (hr : 1 <= r) : cell2TightLog r = ((r - 1) * (r ^ 2 + 10 * r + 1)) / (6 * r * (r + 1)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr; have hr1 : 0 < r + 1 := by linarith
  have hz : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by field_simp [hr1.ne']; ring
  dsimp [cell2TightLog]; rw [hz]; field_simp [hr0.ne', hr1.ne']; ring
private theorem cell2ChartR_eq_ratio {x y : Real} (hx : x ∈ Icc (0 : Real) 1) : cell2ChartR x y = cell2N x y / cell2D x := by
  have hu : cell2U x ∈ Icc (319999 / 1500000 : Real) (43 / 200) := by norm_num [cell2U] at hx ⊢; constructor <;> nlinarith
  have hu0 : 0 < cell2U x := by norm_num [cell2U] at hx ⊢; linarith
  have he : 0 < cell2E x := by norm_num [cell2E, cell2U] at hx ⊢; linarith
  have hdenpos : 0 < (319999 - cell2U x * 500000 : Real) := by
    norm_num [cell2E] at he ⊢
    linarith
  have hden : (319999 - cell2U x * 500000 : Real) ≠ 0 := hdenpos.ne'
  dsimp [cell2ChartR, cell2RLower, cell2RUpper]
  unfold cell2N cell2D cell2Low cell2Sn cell2Ell cell2E
  field_simp [hu0.ne', he.ne', hden];
    simp only [cell2Low, cell2Ell, cell2E, cell2U]; ring
private theorem cell2ChartR_ge_one {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 1 <= cell2ChartR x y := by
  rw [cell2ChartR_eq_ratio hx]
  have hpos := cell2Factors_pos hx hy
  rcases hpos with ⟨hu, hell, he, hsn, hlow, hn, hd, hnd, hq⟩
  have huquarter : cell2U x <= (1 / 4 : Real) := by norm_num [cell2U] at hx ⊢; linarith
  have huell : cell2U x ≤ cell2Ell x := by unfold cell2Ell; linarith
  have hlowd : cell2D x <= cell2Low x := by unfold cell2D cell2Low; have := mul_le_mul_of_nonneg_right huell he.le; simpa [mul_comm] using this
  have hndge : cell2D x <= cell2N x y := le_trans hlowd (le_add_of_nonneg_right (mul_nonneg hsn hy.1))
  exact (le_div_iff₀ hd).2 (by simpa using hndge)
private theorem cell2Transformed_expansion (x y : Real) : sectionSixFirstLowCentralLargeAboveTransformedIntegrand cell2TightLog (2 : Fin 5) x y = (43 / 200 - 319999 / 1500000) * (cell2RUpper (cell2U x) - cell2RLower (cell2U x)) * (cell2TightLog (cell2ChartR x y) / (cell2U x * (1 - cell2U x) * (cell2ChartR x y + 1))) := by
  have huform : cell2U x = 319999 / 1500000 + 2501 / 1500000 * x := by
    norm_num [cell2U]
  simp only [sectionSixFirstLowCentralLargeAboveTransformedIntegrand, cell2ChartR,
    cell2RLower, cell2RUpper]
  norm_num; rw [huform]
private theorem cell2Transformed_eq_quotient {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        cell2TightLog (2 : Fin 5) x y = cell2P x y / cell2Q x y := by
  rcases cell2Factors_pos hx hy with ⟨hu0, hell, he, hsn, hlow, hn, hd, hnd, hq⟩
  have hell' : 0 < 1 - 3 * cell2U x := by simpa [cell2Ell] using hell
  have huq : cell2U x < 1 := by linarith
  have huq1 : 0 < (1 - cell2U x : Real) := sub_pos.mpr huq
  let r : Real := cell2N x y / cell2D x
  have hr : 0 < r := div_pos hn hd
  have hrc : cell2ChartR x y = r := by
    rw [cell2ChartR_eq_ratio hx]
  have hrOne : 1 ≤ r := by
    rw [← hrc]
    exact cell2ChartR_ge_one hx hy
  have hspan : cell2RUpper (cell2U x) - cell2RLower (cell2U x) =
      cell2Sn x / cell2D x := by
    have hdenpos : 0 < (319999 - cell2U x * 500000 : Real) := by
      norm_num [cell2E] at he ⊢
      linarith
    have hden : (319999 - cell2U x * 500000 : Real) ≠ 0 := hdenpos.ne'
    have huq : cell2U x < 1 := by
      norm_num [cell2Ell] at hell ⊢
      linarith
    have hsubpos : 0 < (1 - cell2U x : Real) := sub_pos.mpr huq
    have hsub : (1 - cell2U x : Real) ≠ 0 := hsubpos.ne'
    unfold cell2RUpper cell2RLower cell2D cell2Sn cell2Low cell2Ell cell2E
    field_simp [hu0.ne', he.ne', hden, hsub]; ring
  have hone : r + 1 =
      (cell2N x y + cell2D x) / cell2D x := by
    dsimp [r]
    field_simp [hd.ne']
  have hlog : cell2TightLog r =
      cell2Ph x y /
        (4 * cell2D x * cell2N x y * (cell2N x y + cell2D x)) := by
    rw [cell2TightLog_eq_ratio hrOne]
    dsimp [r]
    unfold cell2Ph
    field_simp [hn.ne', hd.ne', hnd.ne']; ring
  rw [cell2Transformed_expansion, hrc, hspan, hlog, hone]
  field_simp [hu0.ne', hell.ne', he.ne', hn.ne', hd.ne', hnd.ne', hq.ne', huq1.ne'];
    unfold cell2P cell2Q cell2D; ring
private noncomputable def cell2QuotientNegativeSecondNumerator (p q : Polynomial Real) (x : Real) : Real := -(p.derivative.derivative.eval x * q.eval x ^ 2 - 2 * p.derivative.eval x * q.eval x * q.derivative.eval x + 2 * p.eval x * q.derivative.eval x ^ 2 - p.eval x * q.eval x * q.derivative.derivative.eval x)
private theorem cell2SignedCurvature_evaluation (x y : Real) : (cell2Specialize cell2SignedCurvature y).eval x = cell2QuotientNegativeSecondNumerator (cell2Specialize cell2RationalPolynomials.1 y) (cell2Specialize cell2RationalPolynomials.2 y) x := by simp [cell2Specialize, cell2SignedCurvature, cell2Constant, cell2QuotientNegativeSecondNumerator, Polynomial.derivative_map]
private theorem concaveOn_polynomial_quotient
    (p q : Polynomial Real)
    (hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x)
    (hsigned : ∀ x ∈ Icc (0 : Real) 1,
      0 ≤ cell2QuotientNegativeSecondNumerator p q x) :
    ConcaveOn Real (Icc (0 : Real) 1) (fun x => p.eval x / q.eval x) := by
  let f1 : Real → Real := fun x =>
    (p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) /
      q.eval x ^ 2
  let f2 : Real → Real := fun x =>
    -cell2QuotientNegativeSecondNumerator p q x / q.eval x ^ 3
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
    (convex_Icc (0 : Real) 1)
  · intro x hx
    have hp : HasDerivAt (fun t => p.eval t) (p.derivative.eval x) x :=
      Polynomial.hasDerivAt p x
    have hq0 : HasDerivAt (fun t => q.eval t) (q.derivative.eval x) x :=
      Polynomial.hasDerivAt q x
    exact (hp.continuousAt.div hq0.continuousAt (hq x hx).ne').continuousWithinAt
  · intro x hx
    have hmem := interior_subset hx
    have hp : HasDerivAt (fun t => p.eval t) (p.derivative.eval x) x :=
      Polynomial.hasDerivAt p x
    have hq0 : HasDerivAt (fun t => q.eval t) (q.derivative.eval x) x :=
      Polynomial.hasDerivAt q x
    exact ((hp.div hq0 (hq x hmem).ne').congr_deriv (by
      dsimp [f1])).hasDerivWithinAt
  · intro x hx
    have hmem := interior_subset hx
    have hqx := hq x hmem
    have hp : HasDerivAt (fun t => p.eval t) (p.derivative.eval x) x :=
      Polynomial.hasDerivAt p x
    have hpd : HasDerivAt (fun t => p.derivative.eval t)
        (p.derivative.derivative.eval x) x := Polynomial.hasDerivAt p.derivative x
    have hq0 : HasDerivAt (fun t => q.eval t) (q.derivative.eval x) x :=
      Polynomial.hasDerivAt q x
    have hqd : HasDerivAt (fun t => q.derivative.eval t)
        (q.derivative.derivative.eval x) x := Polynomial.hasDerivAt q.derivative x
    have hnum := (hpd.mul hq0).sub (hp.mul hqd)
    have hden := hq0.pow 2
    exact (hnum.div hden (pow_ne_zero 2 hqx.ne')).congr_deriv (by
      dsimp [f1, f2, cell2QuotientNegativeSecondNumerator]
      field_simp [hqx.ne']; ring) |>.hasDerivWithinAt
  · intro x hx
    have hmem := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hsigned x hmem)) (pow_nonneg (hq x hmem).le 3)
theorem sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell2
    (y : Real) (hy : y ∈ Icc (0 : Real) 1) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ConcaveOn Real (Icc (0 : Real) 1)
      (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        tightLog (2 : Fin 5) x y) := by
  dsimp only
  let p := cell2Specialize cell2RationalPolynomials.1 y
  let q := cell2Specialize cell2RationalPolynomials.2 y
  have heval (x : Real) := cell2Polynomial_evaluation x y
  have hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x := by
    intro x hx
    dsimp [q]
    rw [(heval x).2]
    exact (cell2Factors_pos hx hy).2.2.2.2.2.2.2.2
  have hsigned : ∀ x ∈ Icc (0 : Real) 1,
      0 <= cell2QuotientNegativeSecondNumerator p q x := by
    intro x hx
    dsimp [p, q]
    rw [← cell2SignedCurvature_evaluation]
    exact cell2SignedCurvature_nonneg hx hy
  refine (concaveOn_polynomial_quotient p q hq hsigned).congr ?_
  intro x hx
  dsimp [p, q]
  rw [(heval x).1, (heval x).2]
  exact (cell2Transformed_eq_quotient hx hy).symm
end
end PrimesRestrictedDigits
