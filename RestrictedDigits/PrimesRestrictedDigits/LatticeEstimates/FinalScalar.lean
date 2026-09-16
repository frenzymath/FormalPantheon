import PrimesRestrictedDigits.LatticeEstimates.FinalScalarResidual

/-!
# Final scalar form of the lattice-sum estimate

This file assembles both dominance branches of published Lemma 14.4 with all coefficients
normalized and both divisor losses explicit.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The coefficient-normalized, pure-real core of published Lemma 14.4. -/
theorem exists_latticeFinalScalarBound
    (A : Real) (hA : 1 <= A) :
    ∃ C : Real, 0 < C ∧
      ∀ (X P Q E D0 D1 G S1 S2 S3 : Real),
        1 <= X -> 1 <= P -> 1 <= Q -> 1 <= E ->
        1 <= D0 -> 1 <= D1 -> 1 <= G ->
        X ^ (17 / 40 : Real) <= P -> Q * E <= A * X / P ->
        0 <= S1 -> 0 <= S2 -> 0 <= S3 ->
        S1 <= (Q * E) ^ largeSieveAlpha ->
        S1 <=
          Q ^ hybridResidualGrowth * (D0 * D1 * E) ^ largeSieveAlpha +
            Q * E * (D0 * D1) ^ (1 / 2 : Real) /
              X ^ hybridResidualHalfDecay ->
        S2 <= Q ^ latticeSumSaving *
          ((Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^ largeSieveAlpha +
            Q ^ 2 * E / (D0 * D1 * G * X ^ largeSieveSigma)) ->
        S3 <= X ^ (23 / 80 : Real) +
          Q * X ^ (23 / 80 : Real) / (D0 * D1 * P) ->
        min (S1 * S2) (S1 * S3) <=
          C * (Q ^ (1 - latticeSumSaving) *
            E ^ (1 - latticeSumSaving)) := by
  let cFirst : Real := 1 + hybridResidualGrowth + latticeSumSaving +
    latticeSumSaving
  let cSecond : Real := 1 / 2 + latticeSumSaving + latticeSumSaving
  let cThird : Real := 1 + latticeSumSaving
  let C : Real := 8 *
    (1 + A ^ cFirst + A ^ cSecond + A ^ cThird)
  have hA0 : 0 <= A := le_trans (by norm_num) hA
  have hC : 0 < C := by
    dsimp only [C]
    have : 0 <= A ^ cFirst := Real.rpow_nonneg hA0 _
    positivity
  refine ⟨C, hC, ?_⟩
  intro X P Q E D0 D1 G S1 S2 S3
    hX hP hQ hE hD0 hD1 hG hPscale hscale
    hS1Nonneg hS2Nonneg hS3Nonneg hS1Standard hS1Alternative hS2 hS3
  let target : Real :=
    Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)
  let U : Real :=
    Q ^ hybridResidualGrowth * (D0 * D1 * E) ^ largeSieveAlpha
  let V : Real :=
    Q * E * (D0 * D1) ^ (1 / 2 : Real) /
      X ^ hybridResidualHalfDecay
  let H : Real :=
    (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^ largeSieveAlpha
  let T : Real := Q ^ 2 * E / (D0 * D1 * G * X ^ largeSieveSigma)
  let firstResidual : Real :=
    X ^ (23 / 80 : Real) * (Q * E) ^ largeSieveAlpha
  let secondResidual : Real :=
    Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real)
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hscale' : Q * E <= A * X ^ (1 - (17 / 40 : Real)) :=
    latticeScale_le_mul_rpow hA0 hX hPscale hscale
  have htarget : 0 <= target := by
    dsimp only [target]
    positivity
  have hU : 0 <= U := by dsimp only [U]; positivity
  have hV : 0 <= V := by dsimp only [V]; positivity
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hT : 0 <= T := by dsimp only [T]; positivity
  have hFirstResidual : 0 <= firstResidual := by
    dsimp only [firstResidual]
    positivity
  have hSecondResidual : 0 <= secondResidual := by
    dsimp only [secondResidual]
    positivity
  change S1 <= U + V at hS1Alternative
  change S2 <= Q ^ latticeSumSaving * (H + T) at hS2
  by_cases hdominant : V <= U
  · have hS1U : S1 <= 2 * U := by linarith
    have hproduct :
        S1 * S2 <= (2 * U) * (Q ^ latticeSumSaving * (H + T)) :=
      mul_le_mul hS1U hS2 hS2Nonneg (by positivity)
    have hhead : U * (Q ^ latticeSumSaving * H) <= target := by
      dsimp only [U, H, target]
      exact latticeScalarFirstHead_le hQ hE hD0 hD1 hG
    have htail : U * (Q ^ latticeSumSaving * T) <=
        A ^ cFirst * target := by
      dsimp only [U, T, target, cFirst]
      exact latticeScalarFirstTail_le hA hX hQ hE hD0 hD1 hG hscale'
    have hfirstBound :
        S1 * S2 <= 2 * (1 + A ^ cFirst) * target := by
      calc
        S1 * S2 <= (2 * U) * (Q ^ latticeSumSaving * (H + T)) := hproduct
        _ = 2 * (U * (Q ^ latticeSumSaving * H) +
            U * (Q ^ latticeSumSaving * T)) := by ring
        _ <= 2 * (target + A ^ cFirst * target) := by gcongr
        _ = 2 * (1 + A ^ cFirst) * target := by ring
    calc
      min (S1 * S2) (S1 * S3) <= S1 * S2 := min_le_left _ _
      _ <= 2 * (1 + A ^ cFirst) * target := hfirstBound
      _ <= C * target := by
        apply mul_le_mul_of_nonneg_right _ htarget
        dsimp only [C]
        have hASecond : 0 <= A ^ cSecond := Real.rpow_nonneg hA0 _
        have hAThird : 0 <= A ^ cThird := Real.rpow_nonneg hA0 _
        nlinarith [Real.rpow_nonneg hA0 cFirst]
  · have hUDominant : U <= V := le_of_not_ge hdominant
    have hS1V : S1 <= 2 * V := by linarith
    have hinterpolation :
        S1 <= ((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
          (2 * V) ^ (2 / 3 : Real) :=
      le_rpow_one_third_mul_rpow_two_thirds hS1Nonneg (by positivity)
        (by positivity) hS1Standard hS1V
    have htwoPower : (2 : Real) ^ (2 / 3 : Real) <= 2 := by
      calc
        (2 : Real) ^ (2 / 3 : Real) <= 2 ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    have hinterpolation' :
        S1 <= 2 * (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
          V ^ (2 / 3 : Real)) := by
      calc
        S1 <= ((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
            (2 * V) ^ (2 / 3 : Real) := hinterpolation
        _ = ((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
            (2 ^ (2 / 3 : Real) * V ^ (2 / 3 : Real)) := by
          rw [Real.mul_rpow (by norm_num) hV]
        _ <= ((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
            (2 * V ^ (2 / 3 : Real)) := by gcongr
        _ = 2 * (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
            V ^ (2 / 3 : Real)) := by ring
    have hhead :
        Q ^ latticeSumSaving * H *
          (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
            V ^ (2 / 3 : Real)) <= A ^ cSecond * target := by
      dsimp only [H, V, target, cSecond]
      exact latticeScalarSecondHeadAbsorbed_le hA hX hQ hE hD0 hD1 hG hscale'
    have htail : V * (Q ^ latticeSumSaving * T) <= secondResidual := by
      dsimp only [V, T, secondResidual]
      exact latticeScalarSecondTail_le hQ hE hD0 hD1 hG hX
    have hleftBound :
        S1 * S2 <= 2 * A ^ cSecond * target + 2 * secondResidual := by
      calc
        S1 * S2 <= S1 * (Q ^ latticeSumSaving * (H + T)) :=
          mul_le_mul_of_nonneg_left hS2 hS1Nonneg
        _ = S1 * (Q ^ latticeSumSaving * H) +
            S1 * (Q ^ latticeSumSaving * T) := by ring
        _ <= (2 * (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
              V ^ (2 / 3 : Real))) * (Q ^ latticeSumSaving * H) +
            (2 * V) * (Q ^ latticeSumSaving * T) := by gcongr
        _ = 2 * (Q ^ latticeSumSaving * H *
              (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
                V ^ (2 / 3 : Real))) +
            2 * (V * (Q ^ latticeSumSaving * T)) := by ring
        _ <= 2 * (A ^ cSecond * target) + 2 * secondResidual := by gcongr
        _ = 2 * A ^ cSecond * target + 2 * secondResidual := by ring
    have hrightProduct :
        S1 * S3 <= (Q * E) ^ largeSieveAlpha * X ^ (23 / 80 : Real) +
          (2 * V) *
            (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) := by
      calc
        S1 * S3 <= S1 *
            (X ^ (23 / 80 : Real) +
              Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) :=
          mul_le_mul_of_nonneg_left hS3 hS1Nonneg
        _ = S1 * X ^ (23 / 80 : Real) +
            S1 * (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) := by ring
        _ <= (Q * E) ^ largeSieveAlpha * X ^ (23 / 80 : Real) +
            (2 * V) *
              (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) := by gcongr
    have hcross :
        V * (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) <=
          A ^ cThird * target := by
      dsimp only [V, target, cThird]
      exact latticeScalarSThreeCross_le hA hX hP hQ hE hD0 hD1
        hPscale hscale'
    have hrightBound :
        S1 * S3 <= firstResidual + 2 * A ^ cThird * target := by
      calc
        S1 * S3 <= (Q * E) ^ largeSieveAlpha * X ^ (23 / 80 : Real) +
            (2 * V) *
              (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) := hrightProduct
        _ = firstResidual + 2 *
            (V * (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P))) := by
          dsimp only [firstResidual]
          ring
        _ <= firstResidual + 2 * (A ^ cThird * target) := by gcongr
        _ = firstResidual + 2 * A ^ cThird * target := by ring
    have hresidual : min firstResidual secondResidual <= target := by
      dsimp only [firstResidual, secondResidual, target]
      exact latticeScalarResidualMinimum_le hX hQ hE
    have hminimum :
        min (S1 * S2) (S1 * S3) <=
          (2 * A ^ cSecond + 2 * A ^ cThird) * target +
            2 * min firstResidual secondResidual := by
      by_cases hResidualOrder : firstResidual <= secondResidual
      · rw [min_eq_left hResidualOrder]
        calc
          min (S1 * S2) (S1 * S3) <= S1 * S3 := min_le_right _ _
          _ <= firstResidual + 2 * A ^ cThird * target := hrightBound
          _ <= (2 * A ^ cSecond + 2 * A ^ cThird) * target +
              2 * firstResidual := by
            have hASecond : 0 <= A ^ cSecond := Real.rpow_nonneg hA0 _
            nlinarith
      · have hResidualOrder' : secondResidual <= firstResidual :=
          le_of_not_ge hResidualOrder
        rw [min_eq_right hResidualOrder']
        calc
          min (S1 * S2) (S1 * S3) <= S1 * S2 := min_le_left _ _
          _ <= 2 * A ^ cSecond * target + 2 * secondResidual := hleftBound
          _ <= (2 * A ^ cSecond + 2 * A ^ cThird) * target +
              2 * secondResidual := by
            have hAThird : 0 <= A ^ cThird := Real.rpow_nonneg hA0 _
            nlinarith
    calc
      min (S1 * S2) (S1 * S3) <=
          (2 * A ^ cSecond + 2 * A ^ cThird) * target +
            2 * min firstResidual secondResidual := hminimum
      _ <= (2 * A ^ cSecond + 2 * A ^ cThird) * target + 2 * target := by
        gcongr
      _ <= C * target := by
        rw [show
          (2 * A ^ cSecond + 2 * A ^ cThird) * target + 2 * target =
            (2 * A ^ cSecond + 2 * A ^ cThird + 2) * target by ring]
        have hAFirst : 0 <= A ^ cFirst := Real.rpow_nonneg hA0 _
        have hASecond : 0 <= A ^ cSecond := Real.rpow_nonneg hA0 _
        have hAThird : 0 <= A ^ cThird := Real.rpow_nonneg hA0 _
        have hcoefficient :
            2 * A ^ cSecond + 2 * A ^ cThird + 2 <= C := by
          calc
            2 * A ^ cSecond + 2 * A ^ cThird + 2 =
                2 * (1 + A ^ cSecond + A ^ cThird) := by ring
            _ <= 2 * (1 + A ^ cFirst + A ^ cSecond + A ^ cThird) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              linarith
            _ <= 8 * (1 + A ^ cFirst + A ^ cSecond + A ^ cThird) := by
              exact mul_le_mul_of_nonneg_right (by norm_num)
                (by positivity)
            _ = C := rfl
        exact mul_le_mul_of_nonneg_right hcoefficient htarget

end

end PrimesRestrictedDigits
