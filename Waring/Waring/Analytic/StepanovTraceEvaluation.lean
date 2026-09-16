import Waring.Analytic.StepanovTracePointPhase

/-!
# Mapped base-field phase polynomials

`StepanovTracePointPhase` identifies the full trace polynomial of the phase
polynomial over an extension field with the algebra trace.  This file gives
the equivalent formulation obtained by first constructing the polynomial
over `ZMod p` and then mapping its coefficients into the extension.  That is
the form needed to keep the original prime-field phase polynomial explicit.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- Mapping a point-phase polynomial maps its coefficient vector. -/
theorem map_pointPhasePolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b : Fin 5 → R) :
    (pointPhasePolynomial b).map f = pointPhasePolynomial (f ∘ b) := by
  change (mapRingHom f) (Finset.univ.sum fun i : Fin 5 ↦
    C (b i) * X ^ (i.val + 1)) =
      Finset.univ.sum fun i : Fin 5 ↦
        C ((f ∘ b) i) * X ^ (i.val + 1)
  rw [map_sum]
  simp

/-- The phase polynomial over `ZMod p`, mapped coefficientwise into an
extension ring. -/
noncomputable def mappedPointPhasePolynomial
    {p : Nat} {E : Type*} [CommRing E] [Algebra (ZMod p) E]
    (b : Fin 5 → ZMod p) : E[X] :=
  (pointPhasePolynomial b).map (algebraMap (ZMod p) E)

/-- The mapped base-field phase polynomial is the phase polynomial of the
mapped coefficient vector. -/
theorem mappedPointPhasePolynomial_eq
    {p : Nat} {E : Type*} [CommRing E] [Algebra (ZMod p) E]
    (b : Fin 5 → ZMod p) :
    mappedPointPhasePolynomial (E := E) b =
      pointPhasePolynomial ((algebraMap (ZMod p) E) ∘ b) :=
  map_pointPhasePolynomial (algebraMap (ZMod p) E) b

/-- For a degree-`2 * m` finite extension, the full trace polynomial of the
mapped base-field phase evaluates to the embedded algebra trace. -/
theorem eval_fullTracePolynomial_mappedPointPhase_eq_algebraMap_trace
    {E : Type*} [Field E] [Finite E] {p m : Nat} [Fact p.Prime]
    [Algebra (ZMod p) E] [CharP E p]
    (hfinrank : Module.finrank (ZMod p) E = 2 * m)
    (b : Fin 5 → ZMod p) (x : E) :
    (fullTracePolynomial p m (mappedPointPhasePolynomial (E := E) b)).eval x =
      algebraMap (ZMod p) E
        (Algebra.trace (ZMod p) E
          (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x)) := by
  rw [mappedPointPhasePolynomial_eq]
  exact eval_fullTracePolynomial_pointPhase_eq_algebraMap_trace
    hfinrank b x

/-- A fiber of the trace polynomial of the mapped base-field phase is the
corresponding algebra-trace fiber. -/
theorem eval_fullTracePolynomial_mappedPointPhase_eq_algebraMap_iff_trace_eq
    {E : Type*} [Field E] [Finite E] {p m : Nat} [Fact p.Prime]
    [Algebra (ZMod p) E] [CharP E p]
    (hfinrank : Module.finrank (ZMod p) E = 2 * m)
    (b : Fin 5 → ZMod p) (x : E) (c : ZMod p) :
    (fullTracePolynomial p m (mappedPointPhasePolynomial (E := E) b)).eval x =
        algebraMap (ZMod p) E c ↔
      Algebra.trace (ZMod p) E
        (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x) = c := by
  rw [eval_fullTracePolynomial_mappedPointPhase_eq_algebraMap_trace hfinrank]
  exact (algebraMap (ZMod p) E).injective.eq_iff

/-- The mapped-base-field trace identity in the chosen extension of degree
`2 * (h + 3)` used by the Stepanov construction. -/
theorem eval_fullTracePolynomial_mappedPointPhase_extension
    (p h : Nat) [Fact p.Prime] (b : Fin 5 → ZMod p)
    (x : FiniteField.Extension (ZMod p) p (2 * (h + 3))) :
    (fullTracePolynomial p (h + 3)
      (mappedPointPhasePolynomial
        (E := FiniteField.Extension (ZMod p) p (2 * (h + 3))) b)).eval x =
      algebraMap (ZMod p)
        (FiniteField.Extension (ZMod p) p (2 * (h + 3)))
        (Algebra.trace (ZMod p)
          (FiniteField.Extension (ZMod p) p (2 * (h + 3)))
          (Weil.pointPhase
            ((algebraMap (ZMod p)
              (FiniteField.Extension (ZMod p) p (2 * (h + 3)))) ∘ b) x)) := by
  rw [mappedPointPhasePolynomial_eq]
  exact eval_fullTracePolynomial_pointPhase_extension p h b x

end Stepanov

end Waring.Analytic
