import PrimesRestrictedDigits.BasicEstimates.LLLIntegralBasisSelection
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module

/-!
# Existence of a rank-two LLL-reduced integral basis

This is the rank-two part. It proves the exact specialized existence conclusion of
`LLL-1982-CWI`, Section 1, by finite minimization and an integral size-reduction shear.
-/

noncomputable section

namespace PrimesRestrictedDigits

open InnerProductSpace

private abbrev E := EuclideanSpace Real (Fin 3)

theorem exists_lllReducedBasis_finTwo
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin 2) Int Lambda) :
    ∃ b : Module.Basis (Fin 2) Int Lambda,
      IsLLLReduced (integralBasisCoe Lambda b) := by
  obtain ⟨c, hcMin⟩ :=
    exists_integralBasis_minimal_at Lambda b0 (0 : Fin 2)
  let mu : Real :=
    inner Real (c 0 : E) (c 1 : E) / ‖(c 0 : E)‖ ^ 2
  let z : Int := round mu
  let b := integralBasisSubtract Lambda c 0 1 (by decide) z
  have hb0 : b 0 = c 0 := by simp [b]
  have hb1 : b 1 = c 1 - z • c 0 := by simp [b]
  have hbNorm : ‖(b 0 : E)‖ <= ‖(b 1 : E)‖ := by
    have hswap := hcMin (b.reindex (Equiv.swap (0 : Fin 2) 1))
    simpa [hb0] using hswap
  have hbReal : LinearIndependent Real (integralBasisCoe Lambda b) :=
    integralBasisCoe_linearIndependent Lambda b
  refine ⟨b, {
    linearIndependent := hbReal
    coefficient_bound := ?_
    lovasz := ?_ }⟩
  · intro i j hji
    have hi : i = 1 := by
      apply Fin.ext
      omega
    have hj : j = 0 := by
      apply Fin.ext
      omega
    subst i
    subst j
    have hc0ne : (c 0 : E) ≠ 0 := by
      exact_mod_cast c.ne_zero 0
    have hnormne : ‖(c 0 : E)‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hc0ne)
    have hgs0 :
        gramSchmidt Real (integralBasisCoe Lambda b) (0 : Fin 2) =
          (b 0 : E) :=
      InnerProductSpace.gramSchmidt_bot Real _
    have hcoeb1 :
        (b 1 : E) = (c 1 : E) - (z : Real) • (c 0 : E) := by
      rw [hb1]
      simp [Int.cast_smul_eq_zsmul]
    have hcoeff :
        lllCoefficient (integralBasisCoe Lambda b) 1 0 =
          mu - (z : Real) := by
      rw [lllCoefficient, hgs0, hb0]
      change inner Real (c 0 : E) (b 1 : E) / ‖(c 0 : E)‖ ^ 2 = _
      rw [hcoeb1]
      dsimp [integralBasisCoe, mu]
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hnormne]
    rw [hcoeff]
    exact abs_sub_round mu
  · intro i hi
    have hi0 : i = 0 := by
      apply Fin.ext
      omega
    subst i
    let v := integralBasisCoe Lambda b
    have hdecomp := eq_gramSchmidt_add_sum v (1 : Fin 2)
    have hIio : Finset.Iio (1 : Fin 2) = {0} := by decide
    have hsum :
        gramSchmidt Real v (1 : Fin 2) +
            lllCoefficient v 1 0 • gramSchmidt Real v 0 = v 1 := by
      symm
      simpa [hIio] using hdecomp
    change (3 / 4 : Real) * ‖gramSchmidt Real v 0‖ ^ 2 <=
      ‖gramSchmidt Real v 1 +
          lllCoefficient v 1 0 • gramSchmidt Real v 0‖ ^ 2
    rw [hsum]
    have hgs0 : gramSchmidt Real v (0 : Fin 2) = v 0 :=
      InnerProductSpace.gramSchmidt_bot Real _
    rw [hgs0]
    have hsq : ‖v 0‖ ^ 2 <= ‖v 1‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbNorm
    nlinarith [sq_nonneg ‖v 0‖]

end PrimesRestrictedDigits
