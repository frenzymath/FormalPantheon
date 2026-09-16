import PrimesRestrictedDigits.BasicEstimates.LLLIntegralBasisSelection

/-!
# Rank-three LLL coefficient updates under integral shears

The third vector is reduced first along the second basis vector and then along
the first. These identities show that the second shear preserves the already
reduced `mu21` coefficient.
-/

noncomputable section

namespace PrimesRestrictedDigits

open InnerProductSpace

private abbrev E := EuclideanSpace Real (Fin 3)

theorem lllCoefficient_one_zero_eq_firstCoefficient (b : Fin 3 -> E) :
    lllCoefficient b 1 0 = lllFirstCoefficient (b 0) (b 1) := by
  have hg0 : gramSchmidt Real b (0 : Fin 3) = b 0 :=
    InnerProductSpace.gramSchmidt_bot Real b
  simp [lllCoefficient, lllFirstCoefficient, hg0]

theorem gramSchmidt_one_eq_firstRemainder (b : Fin 3 -> E) :
    gramSchmidt Real b 1 = lllFirstRemainder (b 0) (b 1) := by
  have hIio : Finset.Iio (1 : Fin 3) = {0} := by decide
  have hg0 : gramSchmidt Real b (0 : Fin 3) = b 0 :=
    InnerProductSpace.gramSchmidt_bot Real b
  rw [InnerProductSpace.gramSchmidt_def]
  simp [hIio, hg0, lllFirstRemainder, lllFirstCoefficient,
    Submodule.starProjection_singleton]

theorem lllCoefficient_two_one_integralBasisSubtract_one_two
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b : Module.Basis (Fin 3) Int Lambda) (z : Int) :
    lllCoefficient
        (integralBasisCoe Lambda
          (integralBasisSubtract Lambda b 1 2 (by decide) z)) 2 1 =
      lllCoefficient (integralBasisCoe Lambda b) 2 1 - z := by
  let v := integralBasisCoe Lambda b
  let b' := integralBasisSubtract Lambda b 1 2 (by decide) z
  let v' := integralBasisCoe Lambda b'
  have hv0 : v' 0 = v 0 := by
    simp [v', v, b', integralBasisCoe, integralBasisSubtract_apply]
  have hv1 : v' 1 = v 1 := by
    simp [v', v, b', integralBasisCoe]
  have hv2 : v' 2 = v 2 - (z : Real) • v 1 := by
    simpa [v', v, b', integralBasisCoe] using
      coe_integralBasisSubtract_target Lambda b 1 2 (by decide) z
  have hgs1 : gramSchmidt Real v' 1 = gramSchmidt Real v 1 := by
    rw [gramSchmidt_one_eq_firstRemainder,
      gramSchmidt_one_eq_firstRemainder, hv0, hv1]
  have hlin : LinearIndependent Real v :=
    integralBasisCoe_linearIndependent Lambda b
  have hg1ne : gramSchmidt Real v (1 : Fin 3) ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero 1 hlin
  have hnormne : ‖gramSchmidt Real v (1 : Fin 3)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hg1ne)
  have hinner :
      inner Real (gramSchmidt Real v 1) (v 1) =
        ‖gramSchmidt Real v 1‖ ^ 2 := by
    have hdecomp := eq_gramSchmidt_add_sum v (1 : Fin 3)
    have hIio : Finset.Iio (1 : Fin 3) = {0} := by decide
    rw [show v 1 = gramSchmidt Real v 1 +
        lllCoefficient v 1 0 • gramSchmidt Real v 0 by
      simpa [hIio] using hdecomp]
    simp [inner_add_right, inner_smul_right,
      gramSchmidt_orthogonal Real v (by decide : (1 : Fin 3) ≠ 0),
      ]
  rw [lllCoefficient, lllCoefficient]
  change inner Real (gramSchmidt Real v' 1) (v' 2) /
      ‖gramSchmidt Real v' 1‖ ^ 2 =
    inner Real (gramSchmidt Real v 1) (v 2) /
      ‖gramSchmidt Real v 1‖ ^ 2 - (z : Real)
  rw [hgs1, hv2]
  rw [inner_sub_right, inner_smul_right, hinner]
  field_simp [hnormne]

theorem lllCoefficient_two_zero_integralBasisSubtract_zero_two
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b : Module.Basis (Fin 3) Int Lambda) (z : Int) :
    lllCoefficient
        (integralBasisCoe Lambda
          (integralBasisSubtract Lambda b 0 2 (by decide) z)) 2 0 =
      lllCoefficient (integralBasisCoe Lambda b) 2 0 - z := by
  let v := integralBasisCoe Lambda b
  let b' := integralBasisSubtract Lambda b 0 2 (by decide) z
  let v' := integralBasisCoe Lambda b'
  have hv0 : v' 0 = v 0 := by
    simp [v', v, b', integralBasisCoe]
  have hv2 : v' 2 = v 2 - (z : Real) • v 0 := by
    simpa [v', v, b', integralBasisCoe] using
      coe_integralBasisSubtract_target Lambda b 0 2 (by decide) z
  have hgs0 : gramSchmidt Real v' 0 = gramSchmidt Real v 0 := by
    calc
      gramSchmidt Real v' 0 = v' 0 :=
        InnerProductSpace.gramSchmidt_bot Real v'
      _ = v 0 := hv0
      _ = gramSchmidt Real v 0 :=
        (InnerProductSpace.gramSchmidt_bot Real v).symm
  have hlin : LinearIndependent Real v :=
    integralBasisCoe_linearIndependent Lambda b
  have hg0ne : gramSchmidt Real v (0 : Fin 3) ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero 0 hlin
  have hnormne : ‖gramSchmidt Real v (0 : Fin 3)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hg0ne)
  have hg0 : gramSchmidt Real v (0 : Fin 3) = v 0 :=
    InnerProductSpace.gramSchmidt_bot Real v
  have hnormv : ‖v 0‖ ^ 2 ≠ 0 := by simpa [hg0] using hnormne
  rw [lllCoefficient, lllCoefficient]
  change inner Real (gramSchmidt Real v' 0) (v' 2) /
      ‖gramSchmidt Real v' 0‖ ^ 2 =
    inner Real (gramSchmidt Real v 0) (v 2) /
      ‖gramSchmidt Real v 0‖ ^ 2 - (z : Real)
  rw [hgs0, hv2, hg0]
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [sub_div, mul_div_cancel_right₀ _ hnormv]

theorem lllCoefficient_two_one_integralBasisSubtract_zero_two
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b : Module.Basis (Fin 3) Int Lambda) (z : Int) :
    lllCoefficient
        (integralBasisCoe Lambda
          (integralBasisSubtract Lambda b 0 2 (by decide) z)) 2 1 =
      lllCoefficient (integralBasisCoe Lambda b) 2 1 := by
  let v := integralBasisCoe Lambda b
  let b' := integralBasisSubtract Lambda b 0 2 (by decide) z
  let v' := integralBasisCoe Lambda b'
  have hv0 : v' 0 = v 0 := by
    simp [v', v, b', integralBasisCoe]
  have hv1 : v' 1 = v 1 := by
    simp [v', v, b', integralBasisCoe, integralBasisSubtract_apply]
  have hv2 : v' 2 = v 2 - (z : Real) • v 0 := by
    simpa [v', v, b', integralBasisCoe] using
      coe_integralBasisSubtract_target Lambda b 0 2 (by decide) z
  have hgs1 : gramSchmidt Real v' 1 = gramSchmidt Real v 1 := by
    rw [gramSchmidt_one_eq_firstRemainder,
      gramSchmidt_one_eq_firstRemainder, hv0, hv1]
  have horth : inner Real (gramSchmidt Real v 1) (v 0) = 0 :=
    gramSchmidt_inv_triangular Real v (by decide : (0 : Fin 3) < 1)
  rw [lllCoefficient, lllCoefficient]
  change inner Real (gramSchmidt Real v' 1) (v' 2) /
      ‖gramSchmidt Real v' 1‖ ^ 2 =
    inner Real (gramSchmidt Real v 1) (v 2) /
      ‖gramSchmidt Real v 1‖ ^ 2
  rw [hgs1, hv2]
  simp [inner_sub_right, inner_smul_right, horth]

end PrimesRestrictedDigits
