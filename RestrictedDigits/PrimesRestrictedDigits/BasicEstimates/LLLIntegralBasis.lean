import PrimesRestrictedDigits.BasicEstimates.LLLFixedRank
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Integral basis operations for fixed-rank LLL reduction

This file records the lattice-preserving basis operations used. The ambient space is the real
three-space occurring in the paper, while the basis rank remains generic.
-/

noncomputable section

namespace PrimesRestrictedDigits

open Submodule

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The ambient vectors underlying an integral basis of a submodule of real
three-space. -/
def integralBasisCoe {n : Nat} (Lambda : Submodule Int E)
    (b : Module.Basis (Fin n) Int Lambda) : Fin n -> E :=
  fun i => (b i : E)

theorem span_integralBasisCoe {n : Nat} (Lambda : Submodule Int E)
    (b : Module.Basis (Fin n) Int Lambda) :
    Submodule.span Int (Set.range (integralBasisCoe Lambda b)) = Lambda := by
  calc
    Submodule.span Int (Set.range (integralBasisCoe Lambda b)) =
        Submodule.map Lambda.subtype
          (Submodule.span Int (Set.range b)) := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp [integralBasisCoe]
    _ = Lambda := by rw [b.span_eq, Submodule.map_subtype_top]

/-- Every integral basis of a discrete submodule of real three-space is
linearly independent over the reals. -/
theorem integralBasisCoe_linearIndependent {n : Nat}
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b : Module.Basis (Fin n) Int Lambda) :
    LinearIndependent Real (integralBasisCoe Lambda b) := by
  have hspan := span_integralBasisCoe Lambda b
  have hdisc : DiscreteTopology
      (Submodule.span Int (Set.range (integralBasisCoe Lambda b))) := by
    rw [hspan]
    infer_instance
  have hdim := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [hdim, Set.finrank, hspan, Module.finrank_eq_card_basis b]

/-- Subtract an integral multiple of one basis vector from a distinct basis
vector. The result is a basis of the identical integral submodule. -/
def integralBasisSubtract {n : Nat} (Lambda : Submodule Int E)
    (b : Module.Basis (Fin n) Int Lambda) (i j : Fin n) (hij : i ≠ j)
    (z : Int) : Module.Basis (Fin n) Int Lambda :=
  let d : Fin n -> Int := fun k => if k = j then -z else 0
  have hd : d i = 0 := by simp [d, hij]
  b.map (b.repr ≪≫ₗ Finsupp.addSingleEquiv i d hd ≪≫ₗ b.repr.symm)

theorem integralBasisSubtract_apply {n : Nat} (Lambda : Submodule Int E)
    (b : Module.Basis (Fin n) Int Lambda) (i j k : Fin n) (hij : i ≠ j)
    (z : Int) :
    integralBasisSubtract Lambda b i j hij z k =
      b k + (if k = j then -z else 0) • b i := by
  simp [integralBasisSubtract, Module.Basis.map_apply,
    Finsupp.addSingleEquiv]

@[simp] theorem integralBasisSubtract_source {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda)
    (i j : Fin n) (hij : i ≠ j) (z : Int) :
    integralBasisSubtract Lambda b i j hij z i = b i := by
  simp [integralBasisSubtract_apply, hij]

@[simp] theorem integralBasisSubtract_target {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda)
    (i j : Fin n) (hij : i ≠ j) (z : Int) :
    integralBasisSubtract Lambda b i j hij z j = b j - z • b i := by
  simp [integralBasisSubtract_apply, sub_eq_add_neg]

theorem coe_integralBasisSubtract_target {n : Nat}
    (Lambda : Submodule Int E) (b : Module.Basis (Fin n) Int Lambda)
    (i j : Fin n) (hij : i ≠ j) (z : Int) :
    (integralBasisSubtract Lambda b i j hij z j : E) =
      (b j : E) - (z : Real) • (b i : E) := by
  rw [integralBasisSubtract_target]
  simp [Int.cast_smul_eq_zsmul]

/-- A norm-bounded subset of a discrete integral submodule of real
three-space is finite. -/
theorem finite_norm_le_of_discrete_intSubmodule
    (Lambda : Submodule Int E) [DiscreteTopology Lambda] (R : Real) :
    Set.Finite {x : Lambda | ‖(x : E)‖ <= R} := by
  have hfinite :
      Set.Finite (Metric.closedBall (0 : E) R ∩ (Lambda : Set E)) := by
    apply Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall
    exact AddSubgroup.isClosed_of_discrete (H := Lambda.toAddSubgroup)
  apply (hfinite.preimage_embedding (Function.Embedding.subtype _)).subset
  intro x hx
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, x.2⟩

end PrimesRestrictedDigits
