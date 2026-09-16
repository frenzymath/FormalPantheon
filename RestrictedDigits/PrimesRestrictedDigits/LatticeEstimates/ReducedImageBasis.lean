import PrimesRestrictedDigits.LatticeEstimates.DilatedPointSet
import PrimesRestrictedDigits.LatticeEstimates.GeneratingPointDilation
import PrimesRestrictedDigits.LatticeEstimates.ReducedBasisCounting
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

/-!
# A reduced basis for the dilated rank-two lattice

This makes the basis-coordinate and norm-product constants explicit in the
repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Reconstruct an ambient lattice vector using the real casts of its
integral basis coordinates. -/
theorem sum_real_smul_integralBasis_repr
    (L : Submodule Int E) (b : Module.Basis (Fin 2) Int L) (x : L) :
    (∑ i, ((b.repr x i : Int) : Real) • (b i : E)) = (x : E) := by
  calc
    (∑ i, ((b.repr x i : Int) : Real) • (b i : E)) =
        ∑ i, (((b.repr x i : Int) • b i : L) : E) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Int.cast_smul_eq_zsmul]
      rfl
    _ = ((∑ i, (b.repr x i : Int) • b i : L) : E) := by
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      rfl
    _ = (x : E) := by rw [b.sum_repr]

/-- The constant-three coordinate inequality and a `2*N` norm bound give
the required `6*N` bound for each integral coordinate. -/
theorem basis_repr_mul_norm_le_six
    (L : Submodule Int E) (b : Module.Basis (Fin 2) Int L)
    (hweighted : forall a : Fin 2 -> Real,
      ∑ i, ‖a i • (b i : E)‖ <=
        3 * ‖∑ i, a i • (b i : E)‖)
    (N : Real) (x : L) (hx : ‖(x : E)‖ <= 2 * N) (i : Fin 2) :
    ((|b.repr x i| : Int) : Real) * ‖(b i : E)‖ <= 6 * N := by
  let a : Fin 2 -> Real := fun j => (b.repr x j : Int)
  have hterm : ‖a i • (b i : E)‖ <= ∑ j, ‖a j • (b j : E)‖ := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun j _ => norm_nonneg (a j • (b j : E))) (Finset.mem_univ i)
  have hsum := hweighted a
  have hreconstruct : (∑ j, a j • (b j : E)) = (x : E) := by
    exact sum_real_smul_integralBasis_repr L b x
  calc
    ((|b.repr x i| : Int) : Real) * ‖(b i : E)‖ =
        ‖a i • (b i : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      simp [a, Int.cast_abs]
    _ <= ∑ j, ‖a j • (b j : E)‖ := hterm
    _ <= 3 * ‖∑ j, a j • (b j : E)‖ := hsum
    _ = 3 * ‖(x : E)‖ := by rw [hreconstruct]
    _ <= 3 * (2 * N) := mul_le_mul_of_nonneg_left hx (by norm_num)
    _ = 6 * N := by ring

/-- Two ambient-independent lattice vectors cannot both have zero second
coordinate in an integral basis indexed by `Fin 2`. -/
theorem repr_one_ne_zero_of_linearIndependent
    (L : Submodule Int E) (b : Module.Basis (Fin 2) Int L)
    {x y : L}
    (hxy : LinearIndependent Real ![(x : E), (y : E)]) :
    b.repr x 1 ≠ 0 ∨ b.repr y 1 ≠ 0 := by
  by_contra hzero
  push Not at hzero
  have hxsum := sum_real_smul_integralBasis_repr L b x
  have hysum := sum_real_smul_integralBasis_repr L b y
  have hxLine : (x : E) ∈ Real ∙ (b 0 : E) := by
    rw [← hxsum, Fin.sum_univ_two, hzero.1]
    simp only [Int.cast_zero, zero_smul, add_zero]
    rw [Submodule.mem_span_singleton]
    exact ⟨_, rfl⟩
  have hyLine : (y : E) ∈ Real ∙ (b 0 : E) := by
    rw [← hysum, Fin.sum_univ_two, hzero.2]
    simp only [Int.cast_zero, zero_smul, add_zero]
    rw [Submodule.mem_span_singleton]
    exact ⟨_, rfl⟩
  have hb0 : (b 0 : E) ≠ 0 := by
    intro hb
    exact b.ne_zero 0 (Subtype.ext hb)
  let line : Submodule Real E := Real ∙ (b 0 : E)
  let v : Fin 2 -> line := ![⟨(x : E), hxLine⟩, ⟨(y : E), hyLine⟩]
  have hv : LinearIndependent Real v := by
    apply LinearIndependent.of_comp line.subtype
    have heq : line.subtype ∘ v = ![(x : E), (y : E)] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact hxy
  have hdim := hv.fintype_card_le_finrank
  rw [show Module.finrank Real line = 1 by
    exact finrank_span_singleton hb0] at hdim
  norm_num at hdim

end PrimesRestrictedDigits
