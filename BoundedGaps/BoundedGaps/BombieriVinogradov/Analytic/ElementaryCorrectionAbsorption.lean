import BoundedGaps.BombieriVinogradov.Analytic.LogarithmicConductorComposition
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanProgressionConclusion

/-!
# Elementary correction absorption

This file absorbs SEM-567's finite squared-logarithmic correction into one
copy of the same Vaughan Abel envelope that controls the large-conductor
branch. The resulting coefficient is the existing transparent
equation-(1.2) constant.

Sources: `Vaughan1980`, p. 113, and `AkbaryHambrook2013v2`, Theorem 1.3 and
Section 7, pp. 3 and 24--25. The finite two-term composition is
project-derived. Semantic review: `SEM-568`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Absorb the elementary all-modulus correction into the large-conductor
equation-(1.2) coefficient, retaining the small Siegel--Walfisz term exactly. -/
theorem
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_small_add_equationOneTwo :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q : ℕ, siegelWalfiszConductorCutoff D x ≤ Q →
              (Q : ℝ) ≤ Real.sqrt (x : ℝ) →
                (∑ q ∈ Finset.Icc 1 Q,
                  maxCenteredProgressionDiscrepancyUpTo x q) ≤
                  4 * (((siegelWalfiszConductorCutoff D x - 1 : ℕ) : ℝ)) *
                    (1 + Real.log (Q : ℝ)) *
                      (C * ((x : ℝ) * Real.exp
                        (-c * Real.sqrt (Real.log (x : ℝ))))) +
                    vaughanPrimitiveMeanEquationOneTwoConstant
                        (Real.log 4 + 4) *
                      vaughanPrimitiveMeanAbelEnvelope x
                        (siegelWalfiszConductorCutoff D x : ℝ) Q *
                        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  intro D hD
  obtain ⟨C, c, hC, hc, X0, hX0, hcomposition⟩ :=
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_abelEnvelope
      D hD
  refine ⟨C, c, hC, hc, X0, hX0, ?_⟩
  intro x hx Q hcutoffQ hQsqrt
  have hx4 : 4 ≤ x := hX0.trans hx
  have hcutoffOne : 1 ≤ siegelWalfiszConductorCutoff D x :=
    one_le_siegelWalfiszConductorCutoff hD hx4
  have hcutoffOneReal :
      (1 : ℝ) ≤ (siegelWalfiszConductorCutoff D x : ℝ) := by
    exact_mod_cast hcutoffOne
  have hcutoffQReal :
      (siegelWalfiszConductorCutoff D x : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hcutoffQ
  have hcorrection := vaughanPrimitiveMeanElementaryCorrection_le_abelEnvelope
    x Q (siegelWalfiszConductorCutoff D x : ℝ) hx4 hQsqrt
      hcutoffOneReal hcutoffQReal
  have hbase := hcomposition x hx Q hcutoffQ hQsqrt
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          4 * (((siegelWalfiszConductorCutoff D x - 1 : ℕ) : ℝ)) *
            (1 + Real.log (Q : ℝ)) *
              (C * ((x : ℝ) * Real.exp
                (-c * Real.sqrt (Real.log (x : ℝ))))) +
          (5 * vaughanPrimitiveMeanEquationOneOneConstant
              (Real.log 4 + 4)) *
            vaughanPrimitiveMeanAbelEnvelope x
              (siegelWalfiszConductorCutoff D x : ℝ) Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x := hbase
    _ ≤ vaughanPrimitiveMeanAbelEnvelope x
            (siegelWalfiszConductorCutoff D x : ℝ) Q *
            vaughanPrimitiveMeanEquationOneTwoLogPower x +
          4 * (((siegelWalfiszConductorCutoff D x - 1 : ℕ) : ℝ)) *
            (1 + Real.log (Q : ℝ)) *
              (C * ((x : ℝ) * Real.exp
                (-c * Real.sqrt (Real.log (x : ℝ))))) +
          (5 * vaughanPrimitiveMeanEquationOneOneConstant
              (Real.log 4 + 4)) *
            vaughanPrimitiveMeanAbelEnvelope x
              (siegelWalfiszConductorCutoff D x : ℝ) Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x :=
      add_le_add (add_le_add hcorrection le_rfl) le_rfl
    _ = _ := by
      unfold vaughanPrimitiveMeanEquationOneTwoConstant
      ring

end

end BoundedGaps.Maynard
