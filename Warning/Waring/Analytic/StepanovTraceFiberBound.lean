import Waring.Analytic.StepanovAuxiliaryNonvanishing
import Waring.Analytic.StepanovFiberCount
import Waring.Analytic.StepanovPhaseDegree

/-!
# The Stepanov trace-fiber bound

This module instantiates the auxiliary-polynomial construction on the actual
algebraic-trace fibers in the chosen even-degree finite-field extension.
 -/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

/-- The trace fiber of a prime-field point phase in the chosen even-degree
extension has the Stepanov cardinality bound. -/
theorem card_trace_pointPhase_fiber_le
    {p d : Nat} [Fact p.Prime] (hp : 1 < p)
    (hdpos : 0 < d) (hdp : d < p)
    (b : Fin 5 → ZMod p) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (h : Nat) (c : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    (Finset.univ.filter fun x : E ↦
      Algebra.trace (ZMod p) E
        (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x) = c).card ≤
      traceFiberBound p h d := by
  classical
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  letI : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  letI : Fintype E := Fintype.ofFinite E
  let f : E[X] := mappedPointPhasePolynomial (E := E) b
  let points : Finset E := Finset.univ.filter fun x : E ↦
    Algebra.trace (ZMod p) E
      (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x) = c
  have hf : f.natDegree = d := by
    exact natDegree_mappedPointPhasePolynomial_eq b hdpos hd5 hbtop hb
  obtain ⟨a, hane, havanish⟩ :=
    exists_auxiliaryCoefficients_hasse_vanish hp hdp
      (algebraMap (ZMod p) E c) hf.le
  have ha : auxiliaryPolynomial p h f a ≠ 0 :=
    auxiliaryPolynomial_ne_zero Fact.out hdpos hdp hf hane
  have hfinrank : Module.finrank (ZMod p) E = 2 * (h + 3) := by
    simpa [E] using
      FiniteField.finrank_zmod_extension (ZMod p) p (2 * (h + 3))
  have hcard : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x = 0 := by
    intro x hx r hr
    have hxtraceBase :
        Algebra.trace (ZMod p) E
          (Weil.pointPhase ((algebraMap (ZMod p) E) ∘ b) x) = c :=
      (Finset.mem_filter.mp hx).2
    have hxtrace :
        (fullTracePolynomial p (h + 3) f).eval x =
          algebraMap (ZMod p) E c := by
      exact (eval_fullTracePolynomial_mappedPointPhase_eq_algebraMap_iff_trace_eq
        hfinrank b x c).2 hxtraceBase
    have hxpow : x ^ (p ^ (2 * (h + 3))) = x := by
      rw [← hcard]
      exact FiniteField.pow_card x
    exact havanish x hxpow hxtrace r hr
  change points.card ≤ traceFiberBound p h d
  exact card_le_traceFiberBound_of_auxiliary hp.pos hf.le a ha points hvanish

end Stepanov

end Waring.Analytic
