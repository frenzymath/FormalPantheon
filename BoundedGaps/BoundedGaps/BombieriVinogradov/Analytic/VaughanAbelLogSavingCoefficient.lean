import BoundedGaps.BombieriVinogradov.Analytic.VaughanAbelLogSaving

/-!
# Equation-(1.2) coefficient for the Abel-term logarithmic saving

This file multiplies SEM-569's coefficient-free Abel-envelope estimate by the
nonnegative project equation-(1.2) constant. Semantic review: `SEM-569`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- The surviving Abel term in SEM-568 has an `A`th logarithmic saving on the
shared `A+5` conductor and modulus range. -/
theorem exists_vaughanPrimitiveMeanEquationOneTwoAbelTerm_le_logSaving
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ∀ Q : ℕ, siegelWalfiszConductorCutoff (A + 5) x ≤ Q →
          (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) (A + 5) →
            vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
                vaughanPrimitiveMeanAbelEnvelope x
                  (siegelWalfiszConductorCutoff (A + 5) x : ℝ) Q *
                  vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
              (40 * vaughanPrimitiveMeanEquationOneTwoConstant
                (Real.log 4 + 4)) * (x : ℝ) /
                  Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨X0, hX0, hbound⟩ :=
    exists_vaughanPrimitiveMeanAbelEnvelope_mul_logPower_le_logSaving A hA
  refine ⟨X0, hX0, ?_⟩
  intro x hx Q hRQ hQrange
  have hbase := hbound x hx Q hRQ hQrange
  have hconstant :
      0 ≤ vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) := by
    unfold vaughanPrimitiveMeanEquationOneTwoConstant
    have := vaughanPrimitiveMeanEquationOneOneConstant_nonneg
      (Real.log 4 + 4)
    linarith
  calc
    vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
          vaughanPrimitiveMeanAbelEnvelope x
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ) Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x =
        vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
          (vaughanPrimitiveMeanAbelEnvelope x
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ) Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x) := by ring
    _ ≤ vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
        (40 * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) :=
      mul_le_mul_of_nonneg_left hbase hconstant
    _ = (40 * vaughanPrimitiveMeanEquationOneTwoConstant
          (Real.log 4 + 4)) * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) A := by ring

end

end BoundedGaps.Maynard
