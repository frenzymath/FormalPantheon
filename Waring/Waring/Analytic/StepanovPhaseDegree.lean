import Waring.Analytic.StepanovTraceEvaluation
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree of the prime-field phase polynomial

The highest nonzero phase coefficient gives the exact polynomial degree,
and injective coefficient mapping preserves it in every extension field.
 -/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- The point-phase polynomial has exactly its declared highest nonzero
exponent. -/
theorem natDegree_pointPhasePolynomial_eq
    {R : Type*} [CommRing R] [IsDomain R]
    (b : Fin 5 → R) {d : Nat} (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0) :
    (pointPhasePolynomial b).natDegree = d := by
  classical
  let j : Fin 5 := ⟨d - 1, by omega⟩
  have hjval : j.val + 1 = d := by
    dsimp [j]
    omega
  have hdegree : (pointPhasePolynomial b).natDegree ≤ d := by
    rw [pointPhasePolynomial]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    by_cases hid : i.val + 1 ≤ d
    · exact (natDegree_C_mul_X_pow_le (b i) (i.val + 1)).trans hid
    · have hbzero : b i = 0 := hb i (by omega)
      simp only [hbzero, map_zero, zero_mul, natDegree_zero]
      exact Nat.zero_le d
  apply natDegree_eq_of_le_of_coeff_ne_zero hdegree
  rw [pointPhasePolynomial, finsetSum_coeff]
  have hcoeff :
      ∑ i : Fin 5, (C (b i) * X ^ (i.val + 1)).coeff d = b j := by
    calc
      (∑ i : Fin 5, (C (b i) * X ^ (i.val + 1)).coeff d) =
          (C (b j) * X ^ (j.val + 1)).coeff d := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          rw [coeff_C_mul, coeff_X_pow]
          have hne : d ≠ i.val + 1 := by
            intro heq
            apply hij
            apply Fin.ext
            omega
          simp only [hne, if_false, mul_zero]
        · simp
      _ = b j := by
        simp [coeff_C_mul, coeff_X_pow, hjval]
  rw [hcoeff]
  exact hbtop

/-- Mapping the phase polynomial into a nontrivial extension preserves its
declared exact degree. -/
theorem natDegree_mappedPointPhasePolynomial_eq
    {p : Nat} [Fact p.Prime] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (b : Fin 5 → ZMod p)
    {d : Nat} (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0) :
    (mappedPointPhasePolynomial (E := E) b).natDegree = d := by
  rw [mappedPointPhasePolynomial,
    natDegree_map_eq_of_injective (algebraMap (ZMod p) E).injective]
  exact natDegree_pointPhasePolynomial_eq b hdpos hd5 hbtop hb

-- The domain instance is retained in the source-facing degree lemma so its
-- signature stays aligned with the mapped and root-count variants.
attribute [nolint unusedArguments] natDegree_pointPhasePolynomial_eq

end Stepanov

end Waring.Analytic
