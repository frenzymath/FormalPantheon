import Waring.Analytic.StepanovTracePolynomials
import Waring.Analytic.WeilWeights
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace

/-!
# Stepanov trace polynomials and prime-field traces

The full two-half trace polynomial evaluates to the Frobenius-orbit sum of
its input polynomial.  For a point-phase polynomial whose coefficients come
from `ZMod p`, this orbit sum is exactly the algebraic trace of the point
phase from an extension of degree `2 * m`.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- The polynomial whose evaluation is the degree-at-most-five point phase. -/
noncomputable def pointPhasePolynomial
    {E : Type*} [CommRing E] (b : Fin 5 → E) : E[X] :=
  ∑ i : Fin 5, C (b i) * X ^ (i.val + 1)

/-- Evaluating the point-phase polynomial gives `Weil.pointPhase`. -/
@[simp] theorem eval_pointPhasePolynomial
    {E : Type*} [CommRing E] (b : Fin 5 → E) (x : E) :
    (pointPhasePolynomial b).eval x = Weil.pointPhase b x := by
  rw [pointPhasePolynomial, eval_finsetSum]
  simp [Weil.pointPhase]

/-- Evaluation of the low trace polynomial is the first Frobenius-spaced
orbit sum of evaluations. -/
theorem eval_lowTracePolynomial_eq_sum_range
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) (x : E) :
    (lowTracePolynomial p m f).eval x =
      ∑ t ∈ Finset.range m, f.eval (x ^ (p ^ t)) := by
  rw [lowTracePolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t ht
  exact expand_eval (p ^ t) f x

/-- Evaluation of the full trace polynomial is the orbit sum of length
`2 * m`. -/
theorem eval_fullTracePolynomial_eq_sum_range
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) (x : E) :
    (fullTracePolynomial p m f).eval x =
      ∑ t ∈ Finset.range (2 * m), f.eval (x ^ (p ^ t)) := by
  calc
    (fullTracePolynomial p m f).eval x =
        (lowTracePolynomial p m f).eval x +
          (lowTracePolynomial p m f).eval (x ^ (p ^ m)) :=
      eval_fullTracePolynomial p m f x
    _ = (∑ t ∈ Finset.range m, f.eval (x ^ (p ^ t))) +
        ∑ t ∈ Finset.range m,
          f.eval ((x ^ (p ^ m)) ^ (p ^ t)) := by
      rw [eval_lowTracePolynomial_eq_sum_range,
        eval_lowTracePolynomial_eq_sum_range]
    _ = (∑ t ∈ Finset.range m, f.eval (x ^ (p ^ t))) +
        ∑ t ∈ Finset.range m,
          f.eval (x ^ (p ^ (m + t))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [← pow_mul, ← pow_add]
    _ = ∑ t ∈ Finset.range (m + m), f.eval (x ^ (p ^ t)) := by
      rw [Finset.sum_range_add]
    _ = ∑ t ∈ Finset.range (2 * m), f.eval (x ^ (p ^ t)) := by
      rw [two_mul]

/-- Frobenius powers of a point phase with prime-field coefficients act only
on the point. -/
theorem pointPhase_algebraMap_pow_char_pow
    {E : Type*} [CommRing E] {p : Nat} [Fact p.Prime]
    [CharP E p] [Algebra (ZMod p) E]
    (b : Fin 5 → ZMod p) (x : E) (t : Nat) :
    Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x ^ (p ^ t) =
      Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b)
        (x ^ (p ^ t)) := by
  rw [Weil.pointPhase, Weil.pointPhase]
  calc
    (∑ i : Fin 5,
        (algebraMap (ZMod p) E) (b i) * x ^ (i.val + 1)) ^ (p ^ t) =
        ∑ i : Fin 5,
          ((algebraMap (ZMod p) E) (b i) * x ^ (i.val + 1)) ^
            (p ^ t) := by
      simpa using sum_pow_char_pow p t Finset.univ
        (fun i : Fin 5 ↦
          (algebraMap (ZMod p) E) (b i) * x ^ (i.val + 1))
    _ = ∑ i : Fin 5,
        (algebraMap (ZMod p) E) (b i) *
          (x ^ (p ^ t)) ^ (i.val + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, ← map_pow, ZMod.pow_card_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- If `E / ZMod p` has degree `2 * m`, evaluating the full trace polynomial
of the point phase is exactly the image in `E` of the prime-field trace. -/
theorem eval_fullTracePolynomial_pointPhase_eq_algebraMap_trace
    {E : Type*} [Field E] [Finite E] {p m : Nat} [Fact p.Prime]
    [Algebra (ZMod p) E] [CharP E p]
    (hfinrank : Module.finrank (ZMod p) E = 2 * m)
    (b : Fin 5 → ZMod p) (x : E) :
    (fullTracePolynomial p m
      (pointPhasePolynomial ((algebraMap (ZMod p) E) ∘ b))).eval x =
        algebraMap (ZMod p) E
          (Algebra.trace (ZMod p) E
            (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x)) := by
  rw [eval_fullTracePolynomial_eq_sum_range,
    FiniteField.algebraMap_trace_eq_sum_pow, hfinrank]
  apply Finset.sum_congr rfl
  intro t ht
  rw [eval_pointPhasePolynomial, Nat.card_zmod,
    pointPhase_algebraMap_pow_char_pow]

/-- A full-trace polynomial fiber over a prime-field value is exactly the
corresponding algebraic-trace fiber. -/
theorem eval_fullTracePolynomial_pointPhase_eq_algebraMap_iff_trace_eq
    {E : Type*} [Field E] [Finite E] {p m : Nat} [Fact p.Prime]
    [Algebra (ZMod p) E] [CharP E p]
    (hfinrank : Module.finrank (ZMod p) E = 2 * m)
    (b : Fin 5 → ZMod p) (x : E) (c : ZMod p) :
    (fullTracePolynomial p m
      (pointPhasePolynomial ((algebraMap (ZMod p) E) ∘ b))).eval x =
        algebraMap (ZMod p) E c ↔
      Algebra.trace (ZMod p) E
        (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x) = c := by
  rw [eval_fullTracePolynomial_pointPhase_eq_algebraMap_trace hfinrank]
  constructor
  · intro h
    exact (algebraMap (ZMod p) E).injective h
  · intro h
    exact congrArg (algebraMap (ZMod p) E) h

/-- The trace-polynomial identity for the chosen extension of degree
`2 * (h + 3)` used by the Stepanov parameter package. -/
theorem eval_fullTracePolynomial_pointPhase_extension
    (p h : Nat) [Fact p.Prime] (b : Fin 5 → ZMod p)
    (x : FiniteField.Extension (ZMod p) p (2 * (h + 3))) :
    (fullTracePolynomial p (h + 3)
      (pointPhasePolynomial
        ((algebraMap (ZMod p)
          (FiniteField.Extension (ZMod p) p (2 * (h + 3)))) ∘ b))).eval x =
      algebraMap (ZMod p)
        (FiniteField.Extension (ZMod p) p (2 * (h + 3)))
        (Algebra.trace (ZMod p)
          (FiniteField.Extension (ZMod p) p (2 * (h + 3)))
          (Weil.pointPhase
            ((algebraMap (ZMod p)
              (FiniteField.Extension (ZMod p) p (2 * (h + 3)))) ∘ b) x)) := by
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  letI : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  apply eval_fullTracePolynomial_pointPhase_eq_algebraMap_trace
  simpa using
    FiniteField.finrank_zmod_extension (ZMod p) p (2 * (h + 3))

end Stepanov

end Waring.Analytic
