import Waring.Analytic.WeilClosedPoints
import Waring.Analytic.WeilEulerRootIdentity
import Waring.Analytic.WeilTraceBridge

/-!
# Extension-field sums as reciprocal-root power sums

The trace identity makes each extension-field summand depend only on the
minimal polynomial.  Closed-point reindexing then gives the Euler sum, whose
logarithmic derivative is already identified with the negative power sum of
the fixed Artin polynomial's reciprocal roots.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

variable (K : Type*) [Field K] [Fintype K]
variable (p n : Nat) [Fact p.Prime] [CharP K p] [NeZero n]

/-- Classical equality on the finite base field. This instance remains unnamed
to preserve its baseline-recorded generated name. -/
@[nolint defsWithUnderscore]
noncomputable local instance : DecidableEq K := Classical.decEq K

/-- The chosen finite-field extension has a finite enumeration. -/
noncomputable local instance : Fintype (FiniteField.Extension K p n) :=
  Fintype.ofFinite _

/-- The trace-character sum over the chosen degree-`n` extension is the
degree-weighted Euler sum over monic irreducibles whose degrees divide `n`. -/
theorem extensionTraceSum_eq_irreducibleSum
    (character : AddChar K Complex) (b : Fin 5 → K) :
    (∑ x : FiniteField.Extension K p n,
      character
        (Algebra.trace K (FiniteField.Extension K p n)
          (pointPhase
            ((algebraMap K (FiniteField.Extension K p n)) ∘ b) x))) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : Complex) *
            formalRootWeight character b P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  calc
    (∑ x : FiniteField.Extension K p n,
      character
        (Algebra.trace K (FiniteField.Extension K p n)
          (pointPhase
            ((algebraMap K (FiniteField.Extension K p n)) ∘ b) x))) =
        ∑ x : FiniteField.Extension K p n,
          formalRootWeight character b (minpoly K x) ^
            (n / (minpoly K x).natDegree) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [FiniteField.finrank_extension K p n] using
        character_trace_pointPhase_eq_formalRootWeight_pow_div_natDegree_of_root_finite
          character b (minpoly K x)
            (minpoly.irreducible (IsGalois.integral K x))
            (minpoly.monic (IsGalois.integral K x)) x
            (minpoly.aeval K x)
    _ = _ := sum_extension_minpolyWeight_eq_irreducibleSum K p n character b

/-- Exact extension-field power-sum formula for the reciprocal roots of the
Artin coefficient polynomial. -/
theorem extensionTraceSum_eq_neg_artinRootPowerSum
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) :
    (∑ x : FiniteField.Extension K p n,
      character
        (Algebra.trace K (FiniteField.Extension K p n)
          (pointPhase
            ((algebraMap K (FiniteField.Extension K p n)) ∘ b) x))) =
      -((artinLPolynomial character b d).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [extensionTraceSum_eq_irreducibleSum K p n character b]
  exact irreducible_sum_eq_neg_artinRootPowerSum
    character hcharacter b hdpos hd5 hbtop hb hdcast le_rfl (NeZero.ne n)

end Weil

end Waring.Analytic
