import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Data
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TensorPowerBridge
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedPowerBridge
/-!
# The tight curvature certificate for the first large-above cell

The numerical tensor and signed certificates are supplied by the checked
Cell0 certificate shards.  This facade retains the analytic quotient argument
and the original public theorem.
-/
open Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
open SectionSixFirstLowCentralLargeAboveCell0Certificate

private theorem cell0Tensor_eq_power : cell0Tensor = cell0Power :=
  cell0Tensor_eq_power_cached

private theorem cell0Signed_eq_power : cell0SignedCurvature = cell0Power :=
  cell0SignedCurvature_eq_power_cached

private noncomputable def cell0Specialize (p : BivariateRat) (y : Real) : Polynomial Real := p.map (Polynomial.eval₂RingHom (algebraMap Rat Real) y)
private theorem cell0SignedCurvature_nonneg {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 ≤ (cell0Specialize cell0SignedCurvature y).eval x := by have h := tensorBernsteinPolynomial_eval₂_nonneg (n := 11) (m := 21) (coefficient := cell0BernsteinCoefficient) cell0BernsteinCoefficient_nonneg hy.1 hy.2 hx.1 hx.2; change 0 ≤ Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap Rat Real) y) x cell0Tensor at h; rw [cell0Tensor_eq_power, ← cell0Signed_eq_power] at h; simpa [cell0Specialize, Polynomial.eval₂_eq_eval_map] using h
private def cell0U (x : Real) : Real := 43 / 200 + (470003 / 1500000 - 43 / 200) * x
private def cell0E (x : Real) : Real := cell0U x + 180001 / 500000 - 37501 / 250000
private def cell0M (x y : Real) : Real := 212499 / 500000 + (cell0E x - 212499 / 500000) * y
private def cell0N (x y : Real) : Real := 2 * (287501 / 500000 - cell0U x) * cell0M x y
private def cell0D (x : Real) : Real := cell0E x * (212499 / 500000)
private def cell0A (x y : Real) : Real := (cell0U x - 287501 / 500000) * cell0D x + (212499 / 500000) * cell0N x y
private def cell0Ph (x y : Real) : Real := (-2 / 3) * cell0D x ^ 3 - 6 * cell0N x y * cell0D x ^ 2 + 6 * cell0N x y ^ 2 * cell0D x + (2 / 3) * cell0N x y ^ 3
private def cell0P (x y : Real) : Real := (470003 / 1500000 - 43 / 200) * (cell0E x - 212499 / 500000) * cell0Ph x y
private def cell0Q (x y : Real) : Real := 4 * cell0U x * cell0M x y * (cell0N x y + cell0D x) ^ 2 * cell0A x y
private theorem cell0Polynomial_evaluation (x y : Real) : (cell0Specialize cell0RationalPolynomials.1 y).eval x = cell0P x y ∧ (cell0Specialize cell0RationalPolynomials.2 y).eval x = cell0Q x y := by
  constructor <;> norm_num [cell0Specialize, cell0RationalPolynomials, cell0RatA, cell0RatPh, cell0RatD, cell0RatN, cell0RatM, cell0RatE, cell0RatU, cell0RatX, cell0RatY, cell0Constant, cell0P, cell0Q, cell0Ph, cell0A, cell0D, cell0N, cell0M, cell0E, cell0U, Polynomial.coe_eval₂RingHom] <;> ring
private theorem cell0Factors_pos {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : 0 < cell0U x ∧ 0 < cell0E x ∧ 0 < cell0M x y ∧ 0 < cell0N x y ∧ 0 < cell0D x ∧ 0 < cell0N x y + cell0D x ∧ 0 < cell0A x y ∧ 0 < cell0Q x y := by
  rcases hx with ⟨hx0, hx1⟩; rcases hy with ⟨hy0, hy1⟩
  have hu : 0 < cell0U x := by norm_num [cell0U]; linarith
  have he : 0 < cell0E x := by norm_num [cell0E, cell0U]; linarith
  have heb : 0 ≤ cell0E x - 212499 / 500000 := by norm_num [cell0E, cell0U]; nlinarith
  have hm : 0 < cell0M x y := by unfold cell0M; positivity
  have hcu : 0 < 287501 / 500000 - cell0U x := by norm_num [cell0U]; linarith
  have hn : 0 < cell0N x y := by unfold cell0N; positivity
  have hd : 0 < cell0D x := by unfold cell0D; positivity
  have htwo : 0 < 2 * cell0M x y - cell0E x := by norm_num [cell0M, cell0E, cell0U] at *; nlinarith
  have ha : 0 < cell0A x y := by rw [show cell0A x y = (212499 / 500000) * (287501 / 500000 - cell0U x) * (2 * cell0M x y - cell0E x) by simp only [cell0A, cell0D, cell0N]; ring]; positivity
  have hq : 0 < cell0Q x y := by unfold cell0Q; positivity
  exact ⟨hu, he, hm, hn, hd, add_pos hn hd, ha, hq⟩
private noncomputable def cell0QuotientNegativeSecondNumerator (p q : Polynomial Real) (x : Real) : Real := -(p.derivative.derivative.eval x * q.eval x ^ 2 - 2 * p.derivative.eval x * q.eval x * q.derivative.eval x + 2 * p.eval x * q.derivative.eval x ^ 2 - p.eval x * q.eval x * q.derivative.derivative.eval x)
private theorem cell0SignedCurvature_evaluation (x y : Real) : (cell0Specialize cell0SignedCurvature y).eval x = cell0QuotientNegativeSecondNumerator (cell0Specialize cell0RationalPolynomials.1 y) (cell0Specialize cell0RationalPolynomials.2 y) x := by
  simp only [cell0Specialize, cell0SignedCurvature,
    cell0QuotientNegativeSecondNumerator, Polynomial.derivative_map]
  norm_num [cell0Constant, Polynomial.C_ofNat]
private theorem concaveOn_polynomial_quotient (p q : Polynomial Real) (hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x) (hsigned : ∀ x ∈ Icc (0 : Real) 1, 0 ≤ cell0QuotientNegativeSecondNumerator p q x) : ConcaveOn Real (Icc (0 : Real) 1) (fun x => p.eval x / q.eval x) := by
  let f1 : Real → Real := fun x => (p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2
  let f2 : Real → Real := fun x => -cell0QuotientNegativeSecondNumerator p q x / q.eval x ^ 3
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2) (convex_Icc (0 : Real) 1)
  · intro x hx; exact ((Polynomial.hasDerivAt p x).continuousAt.div (Polynomial.hasDerivAt q x).continuousAt (hq x hx).ne').continuousWithinAt
  · intro x hx; exact (((Polynomial.hasDerivAt p x).div (Polynomial.hasDerivAt q x) (hq x (interior_subset hx)).ne').congr_deriv (by dsimp [f1])).hasDerivWithinAt
  · intro x hx
    have hmem := interior_subset hx
    have hqx := hq x hmem
    have hp := Polynomial.hasDerivAt p x
    have hpd := Polynomial.hasDerivAt p.derivative x
    have hq0 := Polynomial.hasDerivAt q x
    have hqd := Polynomial.hasDerivAt q.derivative x
    have hnum := (hpd.mul hq0).sub (hp.mul hqd)
    have hden := hq0.pow 2
    exact (hnum.div hden (pow_ne_zero 2 hqx.ne')).congr_deriv (by
      dsimp [f1, f2, cell0QuotientNegativeSecondNumerator]
      field_simp [hqx.ne']; ring) |>.hasDerivWithinAt
  · intro x hx; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hsigned x (interior_subset hx))) (pow_nonneg (hq x (interior_subset hx)).le 3)
private theorem cell0Transformed_eq_quotient {x y : Real} (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) : let tightLog : Real -> Real := fun r => let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2))); sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog (0 : Fin 5) x y = cell0P x y / cell0Q x y := by
  rcases cell0Factors_pos hx hy with ⟨hu, he, hm, hn, hd, hnd, ha, hq⟩; let r := cell0N x y / cell0D x; let r0 := (287501 / 500000 - cell0U x) / (212499 / 500000 - (319999 / 500000 - cell0U x) / 2); let r1 := (287501 / 500000 - cell0U x) / (212499 / 500000 - (212499 / 500000) / 2); let rc := r0 + (r1 - r0) * y
  have hr : 0 < r := div_pos hn hd
  have hr0 : r0 = 2 * (287501 / 500000 - cell0U x) / cell0E x := by have hv : 212499 / 500000 - (319999 / 500000 - cell0U x) / 2 = cell0E x / 2 := (by norm_num [cell0E]; ring); dsimp [r0]; rw [hv]; field_simp [he.ne']
  have hr1 : r1 = 2 * (287501 / 500000 - cell0U x) / (212499 / 500000) := by dsimp [r1]; norm_num; ring
  have hrc : rc = r := by dsimp [rc, r]; rw [hr0, hr1]; unfold cell0N cell0D cell0M; field_simp [he.ne']
  have hrs : r1 - r0 = 2 * (287501 / 500000 - cell0U x) * (cell0E x - 212499 / 500000) / cell0D x := by rw [hr0, hr1]; unfold cell0D; field_simp [he.ne']
  have hone : r + 1 = (cell0N x y + cell0D x) / cell0D x := by dsimp [r]; field_simp [hd.ne']
  have hlast : cell0U x + (212499 / 500000) * r - 287501 / 500000 = cell0A x y / cell0D x := by dsimp [r]; unfold cell0A; field_simp [hd.ne']; ring
  have hnRelation : cell0N x y = 2 * (287501 / 500000 - cell0U x) * cell0M x y := rfl
  have hlog : (let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))) = cell0Ph x y / (4 * cell0D x * cell0N x y * (cell0N x y + cell0D x)) := by
    have hrne : r ≠ 0 := hr.ne'; have hrp : r + 1 ≠ 0 := (add_pos hr zero_lt_one).ne'
    have hz : 1 - ((r - 1) / (r + 1)) ^ 2 ≠ 0 := by have hzpos : 0 < 1 - ((r - 1) / (r + 1)) ^ 2 := (by rw [show 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 by field_simp [hrp]; ring]; positivity); exact hzpos.ne'
    have htight : (let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))) = (r - 1) * (r ^ 2 + 10 * r + 1) / (6 * r * (r + 1)) := by
      dsimp only
      field_simp [hrne, hrp, hz]
      ring_nf
      field_simp [hrne]
      ring
    rw [htight]; dsimp [r]; unfold cell0Ph; field_simp [hn.ne', hd.ne', hnd.ne']; ring
  change (470003 / 1500000 - 43 / 200) * (r1 - r0) * ((let z := (rc - 1) / (rc + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))) / (cell0U x * (rc + 1) * (cell0U x + (212499 / 500000) * rc - 287501 / 500000))) = cell0P x y / cell0Q x y
  rw [hrc, hrs, hlog, hone, hlast]; field_simp [hq.ne', hu.ne', hm.ne', hn.ne', hd.ne', hnd.ne', ha.ne']; unfold cell0P cell0Q; rw [hnRelation]; ring
theorem sectionSixFirstLowCentralLargeAbove_tight_concaveOn_x_cell0 (y : Real) (hy : y ∈ Icc (0 : Real) 1) : let tightLog : Real -> Real := fun r => let z := (r - 1) / (r + 1); 2 * (z + z ^ 3 / (3 * (1 - z ^ 2))); ConcaveOn Real (Icc (0 : Real) 1) (fun x => sectionSixFirstLowCentralLargeAboveTransformedIntegrand tightLog (0 : Fin 5) x y) := by
  dsimp only; let p := cell0Specialize cell0RationalPolynomials.1 y; let q := cell0Specialize cell0RationalPolynomials.2 y; have heval (x : Real) := cell0Polynomial_evaluation x y
  have hq : ∀ x ∈ Icc (0 : Real) 1, 0 < q.eval x := by intro x hx; dsimp [q]; rw [(heval x).2]; exact (cell0Factors_pos hx hy).2.2.2.2.2.2.2
  have hsigned : ∀ x ∈ Icc (0 : Real) 1, 0 ≤ cell0QuotientNegativeSecondNumerator p q x := by intro x hx; dsimp [p, q]; rw [← cell0SignedCurvature_evaluation]; exact cell0SignedCurvature_nonneg hx hy
  refine (concaveOn_polynomial_quotient p q hq hsigned).congr ?_; intro x hx; dsimp [p, q]; rw [(heval x).1, (heval x).2]; exact (cell0Transformed_eq_quotient hx hy).symm
end
end PrimesRestrictedDigits
