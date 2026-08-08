import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite correlation identity

This is the squared-sum expansion used at each Weyl differencing step in
Chen's Lemma 9 [CHEN1964-EN, pp. 1555-1557].
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- The strict upper-triangle correlation sum. -/
def strictUpperCorrelation (z : Nat → Complex) (P : Nat) : Complex :=
  ∑ x ∈ Finset.range P, ∑ y ∈ Finset.range x, z x * conj (z y)

/-- Expanding a squared finite sum separates its diagonal, strict upper
triangle, and conjugate lower triangle. -/
theorem sum_mul_conj_sum_eq_diagonal_add_strictUpper
    (z : Nat → Complex) (P : Nat) :
    (∑ x ∈ Finset.range P, z x) * conj (∑ x ∈ Finset.range P, z x) =
      (∑ x ∈ Finset.range P, z x * conj (z x)) +
        strictUpperCorrelation z P + conj (strictUpperCorrelation z P) := by
  induction P with
  | zero => simp [strictUpperCorrelation]
  | succ P ih =>
      have hupper : strictUpperCorrelation z (P + 1) =
          strictUpperCorrelation z P +
            ∑ y ∈ Finset.range P, z P * conj (z y) := by
        simp [strictUpperCorrelation, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, map_add, hupper]
      simp only [Finset.sum_range_succ, map_add, starRingEnd_apply]
      simp_rw [← Finset.mul_sum]
      simp only [← star_sum]
      simp only [star_mul, star_star]
      linear_combination ih

/-- If every entry has norm one, the norm square is bounded by the diagonal
cardinality plus twice the upper-triangle correlation norm. -/
theorem norm_sum_range_sq_le_add_two_norm_strictUpper
    (z : Nat → Complex) (P : Nat)
    (hz : ∀ x < P, ‖z x‖ = 1) :
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      P + 2 * ‖strictUpperCorrelation z P‖ := by
  have hdiag :
      (∑ x ∈ Finset.range P, z x * conj (z x)) = (P : Complex) := by
    calc
      (∑ x ∈ Finset.range P, z x * conj (z x)) =
          ∑ _x ∈ Finset.range P, (1 : Complex) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Complex.mul_conj']
        have hxP : x < P := Finset.mem_range.mp hx
        rw [hz x hxP]
        norm_num
      _ = (P : Complex) := by simp
  have hnormExpand :
      ‖∑ x ∈ Finset.range P, z x‖ ^ 2 =
        ‖(P : Complex) + strictUpperCorrelation z P +
          conj (strictUpperCorrelation z P)‖ := by
    calc
      ‖∑ x ∈ Finset.range P, z x‖ ^ 2 =
          ‖(∑ x ∈ Finset.range P, z x) *
            conj (∑ x ∈ Finset.range P, z x)‖ := by
        rw [norm_mul, Complex.norm_conj, pow_two]
      _ = ‖(∑ x ∈ Finset.range P, z x * conj (z x)) +
            strictUpperCorrelation z P +
              conj (strictUpperCorrelation z P)‖ := by
        rw [sum_mul_conj_sum_eq_diagonal_add_strictUpper]
      _ = ‖(P : Complex) + strictUpperCorrelation z P +
            conj (strictUpperCorrelation z P)‖ := by rw [hdiag]
  rw [hnormExpand]
  calc
    ‖(P : Complex) + strictUpperCorrelation z P +
        conj (strictUpperCorrelation z P)‖ ≤
      ‖(P : Complex)‖ + ‖strictUpperCorrelation z P‖ +
        ‖conj (strictUpperCorrelation z P)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = P + 2 * ‖strictUpperCorrelation z P‖ := by
      rw [Complex.norm_natCast, Complex.norm_conj]
      ring

/-- For unit-circle phases, each upper-triangle correlation is the
exponential of the phase difference. -/
theorem strictUpperCorrelation_exp_I_mul_eq
    (theta : Nat → Real) (P : Nat) :
    strictUpperCorrelation
        (fun x ↦ Complex.exp (Complex.I * (theta x : Complex))) P =
      ∑ x ∈ Finset.range P, ∑ y ∈ Finset.range x,
        Complex.exp (Complex.I * ((theta x - theta y : Real) : Complex)) := by
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hconjPhase :
      conj (Complex.I * (theta y : Complex)) =
        -Complex.I * (theta y : Complex) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  calc
    Complex.exp (Complex.I * (theta x : Complex)) *
          conj (Complex.exp (Complex.I * (theta y : Complex))) =
        Complex.exp (Complex.I * (theta x : Complex)) *
          Complex.exp (conj (Complex.I * (theta y : Complex))) := by
            rw [Complex.exp_conj]
    _ = Complex.exp
          (Complex.I * (theta x : Complex) +
            conj (Complex.I * (theta y : Complex))) := by
          rw [Complex.exp_add]
    _ = Complex.exp
          (Complex.I * ((theta x - theta y : Real) : Complex)) := by
          congr 1
          rw [hconjPhase]
          push_cast
          ring

/-- The first Weyl-differencing inequality for an arbitrary real phase. -/
theorem norm_sum_range_exp_I_mul_sq_le
    (theta : Nat → Real) (P : Nat) :
    ‖∑ x ∈ Finset.range P,
        Complex.exp (Complex.I * (theta x : Complex))‖ ^ 2 ≤
      P + 2 * ‖∑ x ∈ Finset.range P, ∑ y ∈ Finset.range x,
        Complex.exp (Complex.I * ((theta x - theta y : Real) : Complex))‖ := by
  rw [← strictUpperCorrelation_exp_I_mul_eq]
  exact norm_sum_range_sq_le_add_two_norm_strictUpper _ P fun x _ ↦ by
    exact Complex.norm_exp_I_mul_ofReal (theta x)

end Waring.Analytic
