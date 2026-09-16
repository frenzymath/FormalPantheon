import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankExistenceThree
import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankExistenceTwo
import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankThree
import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankTwo
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Sorted integral bases with fixed-rank coordinate bounds

The coordinate estimate is permutation-invariant. The sorted basis is not
asserted to remain LLL-reduced.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Reindex an integral basis by the permutation sorting its ambient norms. -/
def integralBasisSortedByNorm {n : Nat} (Lambda : Submodule Int E)
    (b : Module.Basis (Fin n) Int Lambda) :
    Module.Basis (Fin n) Int Lambda :=
  b.reindex (Tuple.sort fun i => ‖(b i : E)‖).symm

@[simp] theorem integralBasisSortedByNorm_apply {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda)
    (i : Fin n) :
    integralBasisSortedByNorm Lambda b i =
      b (Tuple.sort (fun j => ‖(b j : E)‖) i) := by
  simp [integralBasisSortedByNorm]

theorem integralBasisSortedByNorm_norm_monotone {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda) :
    Monotone fun i => ‖(integralBasisSortedByNorm Lambda b i : E)‖ := by
  intro i j hij
  change ‖(integralBasisSortedByNorm Lambda b i : E)‖ <=
    ‖(integralBasisSortedByNorm Lambda b j : E)‖
  rw [integralBasisSortedByNorm_apply, integralBasisSortedByNorm_apply]
  exact Tuple.monotone_sort (fun k => ‖(b k : E)‖) hij

private theorem weighted_bound_integralBasisSortedByNorm {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda)
    (C : Real)
    (hbound : ∀ a : Fin n -> Real,
      ∑ i, ‖a i • (b i : E)‖ <= C * ‖∑ i, a i • (b i : E)‖) :
    ∀ a : Fin n -> Real,
      ∑ i, ‖a i • (integralBasisSortedByNorm Lambda b i : E)‖ <=
        C * ‖∑ i, a i • (integralBasisSortedByNorm Lambda b i : E)‖ := by
  intro a
  let sigma : Equiv.Perm (Fin n) := Tuple.sort fun i => ‖(b i : E)‖
  let c : Fin n -> Real := fun i => a (sigma.symm i)
  have h := hbound c
  have hleft :
      (∑ i, ‖a i • (integralBasisSortedByNorm Lambda b i : E)‖) =
        ∑ i, ‖c i • (b i : E)‖ := by
    calc
      (∑ i, ‖a i • (integralBasisSortedByNorm Lambda b i : E)‖) =
          ∑ i, ‖c (sigma i) • (b (sigma i) : E)‖ := by
        simp [integralBasisSortedByNorm, sigma, c]
      _ = ∑ i, ‖c i • (b i : E)‖ :=
        Equiv.sum_comp sigma (fun i : Fin n => ‖c i • (b i : E)‖)
  have hright :
      (∑ i, a i • (integralBasisSortedByNorm Lambda b i : E)) =
        ∑ i, c i • (b i : E) := by
    calc
      (∑ i, a i • (integralBasisSortedByNorm Lambda b i : E)) =
          ∑ i, c (sigma i) • (b (sigma i) : E) := by
        simp [integralBasisSortedByNorm, sigma, c]
      _ = ∑ i, c i • (b i : E) :=
        Equiv.sum_comp sigma (fun i : Fin n => c i • (b i : E))
  calc
    (∑ i, ‖a i • (integralBasisSortedByNorm Lambda b i : E)‖) =
        ∑ i, ‖c i • (b i : E)‖ := hleft
    _ <= C * ‖∑ i, c i • (b i : E)‖ := h
    _ = C * ‖∑ i, a i •
        (integralBasisSortedByNorm Lambda b i : E)‖ := by rw [hright]

theorem exists_sortedIntegralBasis_finTwo_of_lllReduced
    (Lambda : Submodule Int E) (b : Module.Basis (Fin 2) Int Lambda)
    (hb : IsLLLReduced (integralBasisCoe Lambda b)) :
    ∃ c : Module.Basis (Fin 2) Int Lambda,
      Monotone (fun i => ‖(c i : E)‖) ∧
      ∀ a : Fin 2 -> Real,
        ∑ i, ‖a i • (c i : E)‖ <=
          3 * ‖∑ i, a i • (c i : E)‖ := by
  let c := integralBasisSortedByNorm Lambda b
  refine ⟨c, integralBasisSortedByNorm_norm_monotone Lambda b, ?_⟩
  apply weighted_bound_integralBasisSortedByNorm Lambda b 3
  simpa [integralBasisCoe] using
    sum_norm_smul_le_three_norm_sum_of_lllReduced
      (integralBasisCoe Lambda b) hb

theorem exists_sortedIntegralBasis_finThree_of_lllReduced
    (Lambda : Submodule Int E) (b : Module.Basis (Fin 3) Int Lambda)
    (hb : IsLLLReduced (integralBasisCoe Lambda b)) :
    ∃ c : Module.Basis (Fin 3) Int Lambda,
      Monotone (fun i => ‖(c i : E)‖) ∧
      ∀ a : Fin 3 -> Real,
        ∑ i, ‖a i • (c i : E)‖ <=
          9 * ‖∑ i, a i • (c i : E)‖ := by
  let c := integralBasisSortedByNorm Lambda b
  refine ⟨c, integralBasisSortedByNorm_norm_monotone Lambda b, ?_⟩
  apply weighted_bound_integralBasisSortedByNorm Lambda b 9
  simpa [integralBasisCoe] using
    sum_norm_smul_le_nine_norm_sum_of_lllReduced
      (integralBasisCoe Lambda b) hb

theorem exists_sortedIntegralBasis_finTwo
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin 2) Int Lambda) :
    ∃ b : Module.Basis (Fin 2) Int Lambda,
      Monotone (fun i => ‖(b i : E)‖) ∧
      ∀ a : Fin 2 -> Real,
        ∑ i, ‖a i • (b i : E)‖ <=
          3 * ‖∑ i, a i • (b i : E)‖ := by
  obtain ⟨b, hb⟩ := exists_lllReducedBasis_finTwo Lambda b0
  exact exists_sortedIntegralBasis_finTwo_of_lllReduced Lambda b hb

theorem exists_sortedIntegralBasis_finThree
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin 3) Int Lambda) :
    ∃ b : Module.Basis (Fin 3) Int Lambda,
      Monotone (fun i => ‖(b i : E)‖) ∧
      ∀ a : Fin 3 -> Real,
        ∑ i, ‖a i • (b i : E)‖ <=
          9 * ‖∑ i, a i • (b i : E)‖ := by
  obtain ⟨b, hb⟩ := exists_lllReducedBasis_finThree Lambda b0
  exact exists_sortedIntegralBasis_finThree_of_lllReduced Lambda b hb

end PrimesRestrictedDigits
