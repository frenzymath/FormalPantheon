import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankExistenceThreeUpdates
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module

/-!
# Existence of a rank-three LLL-reduced integral basis

This is the rank-three part. It proves the exact specialized existence conclusion of
`LLL-1982-CWI`, Section 1, using the independently finite flag-minimization argument.
-/

noncomputable section

namespace PrimesRestrictedDigits

open InnerProductSpace

private abbrev E := EuclideanSpace Real (Fin 3)

theorem exists_lllReducedBasis_finThree
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin 3) Int Lambda) :
    ∃ b : Module.Basis (Fin 3) Int Lambda,
      IsLLLReduced (integralBasisCoe Lambda b) := by
  obtain ⟨c, hcMin⟩ :=
    exists_integralBasis_minimal_at Lambda b0 (0 : Fin 3)
  have hc0ne : (c 0 : E) ≠ 0 := by exact_mod_cast c.ne_zero 0
  let mu10 := lllFirstCoefficient (c 0 : E) (c 1 : E)
  let z10 : Int := round mu10
  let d := integralBasisSubtract Lambda c 0 1 (by decide) z10
  have hd0 : d 0 = c 0 := by simp [d]
  have hd1 :
      (d 1 : E) = (c 1 : E) - (z10 : Real) • (c 0 : E) := by
    simpa [d] using
      coe_integralBasisSubtract_target Lambda c 0 1 (by decide) z10
  have hdReduced :
      |lllFirstCoefficient (d 0 : E) (d 1 : E)| <= 1 / 2 := by
    rw [hd0, hd1, lllFirstCoefficient_sub_smul _ _ hc0ne]
    exact abs_sub_round mu10
  obtain ⟨e, he0, heReduced, heMin⟩ :=
    exists_integralBasis_minimal_second_finThree Lambda d hdReduced
  let z21 : Int := round (lllCoefficient (integralBasisCoe Lambda e) 2 1)
  let f := integralBasisSubtract Lambda e 1 2 (by decide) z21
  let z20 : Int := round (lllCoefficient (integralBasisCoe Lambda f) 2 0)
  let b := integralBasisSubtract Lambda f 0 2 (by decide) z20
  let v := integralBasisCoe Lambda b
  have hb0e : b 0 = e 0 := by
    simp [b, f, integralBasisSubtract_apply]
  have hb1e : b 1 = e 1 := by
    simp [b, f, integralBasisSubtract_apply]
  have hb0d : b 0 = d 0 := hb0e.trans he0
  have hb0c : b 0 = c 0 := hb0d.trans hd0
  have hmu10 : |lllCoefficient v 1 0| <= 1 / 2 := by
    rw [lllCoefficient_one_zero_eq_firstCoefficient]
    simpa [v, integralBasisCoe, hb0e, hb1e] using heReduced
  have hmu20Eq :
      lllCoefficient v 2 0 =
        lllCoefficient (integralBasisCoe Lambda f) 2 0 - z20 := by
    simpa [v, b] using
      lllCoefficient_two_zero_integralBasisSubtract_zero_two Lambda f z20
  have hmu20 : |lllCoefficient v 2 0| <= 1 / 2 := by
    rw [hmu20Eq]
    exact abs_sub_round (lllCoefficient (integralBasisCoe Lambda f) 2 0)
  have hmu21Eq :
      lllCoefficient v 2 1 =
        lllCoefficient (integralBasisCoe Lambda e) 2 1 - z21 := by
    calc
      lllCoefficient v 2 1 =
          lllCoefficient (integralBasisCoe Lambda f) 2 1 := by
        simpa [v, b] using
          lllCoefficient_two_one_integralBasisSubtract_zero_two Lambda f z20
      _ = lllCoefficient (integralBasisCoe Lambda e) 2 1 - z21 := by
        simpa [f] using
          lllCoefficient_two_one_integralBasisSubtract_one_two Lambda e z21
  have hmu21 : |lllCoefficient v 2 1| <= 1 / 2 := by
    rw [hmu21Eq]
    exact abs_sub_round (lllCoefficient (integralBasisCoe Lambda e) 2 1)
  have hbReal : LinearIndependent Real v :=
    integralBasisCoe_linearIndependent Lambda b
  refine ⟨b, {
    linearIndependent := hbReal
    coefficient_bound := ?_
    lovasz := ?_ }⟩
  · intro i j hji
    have hij :
        (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
      omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmu10
    · exact hmu20
    · exact hmu21
  · intro i hi
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl
    · have hswap := hcMin (b.reindex (Equiv.swap (0 : Fin 3) 1))
      have hbNorm : ‖(b 0 : E)‖ <= ‖(b 1 : E)‖ := by
        simpa [hb0c] using hswap
      have hdecomp := eq_gramSchmidt_add_sum v (1 : Fin 3)
      have hIio : Finset.Iio (1 : Fin 3) = {0} := by decide
      have hsum :
          gramSchmidt Real v 1 +
              lllCoefficient v 1 0 • gramSchmidt Real v 0 = v 1 := by
        symm
        simpa [hIio] using hdecomp
      change (3 / 4 : Real) * ‖gramSchmidt Real v 0‖ ^ 2 <=
        ‖gramSchmidt Real v 1 +
            lllCoefficient v 1 0 • gramSchmidt Real v 0‖ ^ 2
      rw [hsum]
      have hgs0 : gramSchmidt Real v (0 : Fin 3) = v 0 :=
        InnerProductSpace.gramSchmidt_bot Real _
      rw [hgs0]
      have hsq : ‖v 0‖ ^ 2 <= ‖v 1‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbNorm
      nlinarith [sq_nonneg ‖v 0‖]
    · let q := b.reindex (Equiv.swap (1 : Fin 3) 2)
      have hq0b : q 0 = b 0 := by
        rw [Module.Basis.reindex_apply]
        congr 1
      have hq0 : q 0 = d 0 := hq0b.trans hb0d
      have hq1 : q 1 = b 2 := by
        rw [Module.Basis.reindex_apply]
        congr 1
      have hqReduced :
          |lllFirstCoefficient (q 0 : E) (q 1 : E)| <= 1 / 2 := by
        have hgs0 : gramSchmidt Real v (0 : Fin 3) = v 0 :=
          InnerProductSpace.gramSchmidt_bot Real _
        have hfirst :
            lllCoefficient v 2 0 =
              lllFirstCoefficient (v 0) (v 2) := by
          simp [lllCoefficient, lllFirstCoefficient, hgs0]
        have hqCoeff :
            lllFirstCoefficient (q 0 : E) (q 1 : E) =
              lllCoefficient v 2 0 := by
          rw [hq0b, hq1]
          change lllFirstCoefficient (v 0) (v 2) = _
          exact hfirst.symm
        rw [hqCoeff]
        exact hmu20
      have hsecond := heMin q hq0 hqReduced
      have hdecomp := eq_gramSchmidt_add_sum v (2 : Fin 3)
      have hIio : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
      have hv2 :
          v 2 = gramSchmidt Real v 2 +
            (lllCoefficient v 2 0 • gramSchmidt Real v 0 +
              lllCoefficient v 2 1 • gramSchmidt Real v 1) := by
        simpa [hIio] using hdecomp
      have hgs0 : gramSchmidt Real v (0 : Fin 3) = v 0 :=
        InnerProductSpace.gramSchmidt_bot Real _
      have hfirst :
          lllFirstCoefficient (v 0) (v 2) = lllCoefficient v 2 0 := by
        simp [lllCoefficient, lllFirstCoefficient, hgs0]
      have hrem :
          lllFirstRemainder (v 0) (v 2) =
            gramSchmidt Real v 2 +
              lllCoefficient v 2 1 • gramSchmidt Real v 1 := by
        rw [lllFirstRemainder, hfirst, hv2, hgs0]
        module
      have hnorm :
          ‖gramSchmidt Real v 1‖ <=
            ‖gramSchmidt Real v 2 +
              lllCoefficient v 2 1 • gramSchmidt Real v 1‖ := by
        have hleft :
            lllFirstRemainder (e 0 : E) (e 1 : E) =
              gramSchmidt Real v 1 := by
          rw [gramSchmidt_one_eq_firstRemainder]
          simp [v, integralBasisCoe, hb0e, hb1e]
        have hright :
            lllFirstRemainder (q 0 : E) (q 1 : E) =
              gramSchmidt Real v 2 +
                lllCoefficient v 2 1 • gramSchmidt Real v 1 := by
          rw [hq0b, hq1]
          change lllFirstRemainder (v 0) (v 2) = _
          exact hrem
        calc
          ‖gramSchmidt Real v 1‖ =
              ‖lllFirstRemainder (e 0 : E) (e 1 : E)‖ := by rw [hleft]
          _ <= ‖lllFirstRemainder (q 0 : E) (q 1 : E)‖ := hsecond
          _ = ‖gramSchmidt Real v 2 +
                lllCoefficient v 2 1 • gramSchmidt Real v 1‖ := by
            rw [hright]
      change (3 / 4 : Real) * ‖gramSchmidt Real v 1‖ ^ 2 <=
        ‖gramSchmidt Real v 2 +
            lllCoefficient v 2 1 • gramSchmidt Real v 1‖ ^ 2
      have hsq :
          ‖gramSchmidt Real v 1‖ ^ 2 <=
            ‖gramSchmidt Real v 2 +
              lllCoefficient v 2 1 • gramSchmidt Real v 1‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
      nlinarith [sq_nonneg ‖gramSchmidt Real v 1‖]

end PrimesRestrictedDigits
