import PrimesRestrictedDigits.LatticeEstimates.FinalScalarFirst

/-!
# Second dominance branch of the final lattice estimate

This file formalizes the one-third/two-thirds interpolation and the two remaining source-scale
absorptions in published Lemma 14.4.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem secondHeadH_eq
    {Q E D0 D1 G : Real}
    (hQ : 0 <= Q) (hE : 0 <= E)
    (hD0 : 0 <= D0) (hD1 : 0 <= D1) (hG : 0 <= G) :
    (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^ largeSieveAlpha =
      (Q ^ (2 * largeSieveAlpha) * E ^ largeSieveAlpha) /
        (D0 ^ largeSieveAlpha * D1 ^ (2 * largeSieveAlpha) *
          G ^ (2 * largeSieveAlpha)) := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (sq_nonneg Q) hE]
  rw [Real.mul_rpow (mul_nonneg hD0 (sq_nonneg D1)) (sq_nonneg G)]
  rw [Real.mul_rpow hD0 (sq_nonneg D1)]
  rw [pow_two_rpow Q largeSieveAlpha hQ,
    pow_two_rpow D1 largeSieveAlpha hD1,
    pow_two_rpow G largeSieveAlpha hG]

private theorem secondHeadStandardInterpolation_eq
    {Q E : Real} (hQ : 0 <= Q) (hE : 0 <= E) :
    ((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) =
      Q ^ (largeSieveAlpha / 3) *
        E ^ (largeSieveAlpha / 3) := by
  rw [Real.mul_rpow hQ hE]
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hE _)]
  rw [rpow_rpow_eq_mul hQ, rpow_rpow_eq_mul hE]
  congr 2 <;> ring

private theorem secondHeadAlternativeInterpolation_eq
    {Q E D0 D1 X : Real}
    (hQ : 0 <= Q) (hE : 0 <= E) (hD0 : 0 <= D0) (hD1 : 0 <= D1)
    (hX : 0 < X) :
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
        X ^ hybridResidualHalfDecay) ^ (2 / 3 : Real) =
      (Q ^ (2 / 3 : Real) * E ^ (2 / 3 : Real) *
          (D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real))) /
        X ^ ((2 / 3 : Real) * hybridResidualHalfDecay) := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (mul_nonneg hQ hE) (Real.rpow_nonneg (by positivity) _)]
  rw [Real.mul_rpow hQ hE]
  rw [rpow_rpow_eq_mul (mul_nonneg hD0 hD1)]
  rw [Real.mul_rpow hD0 hD1]
  rw [rpow_rpow_eq_mul hX.le]
  rw [show (1 / 2 : Real) * (2 / 3) = 1 / 3 by norm_num]
  rw [show hybridResidualHalfDecay * (2 / 3 : Real) =
    (2 / 3) * hybridResidualHalfDecay by ring]

private theorem secondHeadDenominator_le
    {D0 D1 G : Real} (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) :
    D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real) <=
      D0 ^ largeSieveAlpha * D1 ^ (2 * largeSieveAlpha) *
        G ^ (2 * largeSieveAlpha) := by
  have hD0Power :
      D0 ^ (1 / 3 : Real) <= D0 ^ largeSieveAlpha :=
    Real.rpow_le_rpow_of_exponent_le hD0 (by
      norm_num [largeSieveAlpha])
  have hD1Power :
      D1 ^ (1 / 3 : Real) <= D1 ^ (2 * largeSieveAlpha) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by
      norm_num [largeSieveAlpha])
  have hGPower : 1 <= G ^ (2 * largeSieveAlpha) := by
    calc
      (1 : Real) = 1 ^ (2 * largeSieveAlpha) := by rw [Real.one_rpow]
      _ <= G ^ (2 * largeSieveAlpha) :=
        Real.rpow_le_rpow (by norm_num) hG (by
          norm_num [largeSieveAlpha])
  calc
    D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real) <=
        D0 ^ largeSieveAlpha * D1 ^ (2 * largeSieveAlpha) :=
      mul_le_mul hD0Power hD1Power (by positivity) (by positivity)
    _ <= (D0 ^ largeSieveAlpha * D1 ^ (2 * largeSieveAlpha)) *
        G ^ (2 * largeSieveAlpha) := by
      exact le_mul_of_one_le_right (by positivity) hGPower

/-- The interpolated `S2` head has the coarsened powers printed by the
source, with the repaired multiplicity loss retained. -/
theorem latticeScalarSecondHead_le
    {Q E D0 D1 G X : Real}
    (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) (hX : 1 <= X) :
    Q ^ latticeSumSaving *
        (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^ largeSieveAlpha *
      (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
        (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) ^ (2 / 3 : Real)) <=
      Q ^ (3 / 2 + latticeSumSaving) * E ^ (6 / 5 : Real) /
        X ^ (3 / 10 : Real) := by
  have hQPos : 0 < Q := Real.zero_lt_one.trans_le hQ
  have hEPos : 0 < E := Real.zero_lt_one.trans_le hE
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  rw [secondHeadH_eq hQPos.le hEPos.le (by positivity) (by positivity)
    (by positivity)]
  rw [secondHeadStandardInterpolation_eq hQPos.le hEPos.le]
  rw [secondHeadAlternativeInterpolation_eq hQPos.le hEPos.le
    (by positivity) (by positivity) hXPos]
  let denominator : Real :=
    D0 ^ largeSieveAlpha * D1 ^ (2 * largeSieveAlpha) *
      G ^ (2 * largeSieveAlpha)
  have hdenPos : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hdenCancel :
      (D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real)) / denominator <= 1 :=
    (div_le_one hdenPos).2 (secondHeadDenominator_le hD0 hD1 hG)
  have hraw :
      Q ^ latticeSumSaving *
          ((Q ^ (2 * largeSieveAlpha) * E ^ largeSieveAlpha) /
            denominator) *
        ((Q ^ (largeSieveAlpha / 3) * E ^ (largeSieveAlpha / 3)) *
          ((Q ^ (2 / 3 : Real) * E ^ (2 / 3 : Real) *
              (D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real))) /
            X ^ ((2 / 3 : Real) * hybridResidualHalfDecay))) <=
        (Q ^ latticeSumSaving * Q ^ (2 * largeSieveAlpha) *
            Q ^ (largeSieveAlpha / 3) * Q ^ (2 / 3 : Real)) *
          (E ^ largeSieveAlpha * E ^ (largeSieveAlpha / 3) *
            E ^ (2 / 3 : Real)) /
          X ^ ((2 / 3 : Real) * hybridResidualHalfDecay) := by
    calc
      Q ^ latticeSumSaving *
          ((Q ^ (2 * largeSieveAlpha) * E ^ largeSieveAlpha) /
            denominator) *
        ((Q ^ (largeSieveAlpha / 3) * E ^ (largeSieveAlpha / 3)) *
          ((Q ^ (2 / 3 : Real) * E ^ (2 / 3 : Real) *
              (D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real))) /
            X ^ ((2 / 3 : Real) * hybridResidualHalfDecay))) =
        ((Q ^ latticeSumSaving * Q ^ (2 * largeSieveAlpha) *
            Q ^ (largeSieveAlpha / 3) * Q ^ (2 / 3 : Real)) *
          (E ^ largeSieveAlpha * E ^ (largeSieveAlpha / 3) *
            E ^ (2 / 3 : Real)) /
          X ^ ((2 / 3 : Real) * hybridResidualHalfDecay)) *
            ((D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real)) /
              denominator) := by
          field_simp
      _ <= ((Q ^ latticeSumSaving * Q ^ (2 * largeSieveAlpha) *
            Q ^ (largeSieveAlpha / 3) * Q ^ (2 / 3 : Real)) *
          (E ^ largeSieveAlpha * E ^ (largeSieveAlpha / 3) *
            E ^ (2 / 3 : Real)) /
          X ^ ((2 / 3 : Real) * hybridResidualHalfDecay)) * 1 := by gcongr
      _ = _ := by ring
  calc
    Q ^ latticeSumSaving *
        ((Q ^ (2 * largeSieveAlpha) * E ^ largeSieveAlpha) /
          denominator) *
      ((Q ^ (largeSieveAlpha / 3) * E ^ (largeSieveAlpha / 3)) *
        ((Q ^ (2 / 3 : Real) * E ^ (2 / 3 : Real) *
            (D0 ^ (1 / 3 : Real) * D1 ^ (1 / 3 : Real))) /
          X ^ ((2 / 3 : Real) * hybridResidualHalfDecay))) <=
      (Q ^ latticeSumSaving * Q ^ (2 * largeSieveAlpha) *
          Q ^ (largeSieveAlpha / 3) * Q ^ (2 / 3 : Real)) *
        (E ^ largeSieveAlpha * E ^ (largeSieveAlpha / 3) *
          E ^ (2 / 3 : Real)) /
        X ^ ((2 / 3 : Real) * hybridResidualHalfDecay) := hraw
    _ = Q ^ (49 / 33 + latticeSumSaving) * E ^ (262 / 231 : Real) /
        X ^ (20 / 63 : Real) := by
      rw [← Real.rpow_add hQPos, ← Real.rpow_add hQPos,
        ← Real.rpow_add hQPos]
      rw [← Real.rpow_add hEPos, ← Real.rpow_add hEPos]
      rw [show latticeSumSaving + 2 * largeSieveAlpha +
          largeSieveAlpha / 3 + 2 / 3 =
        49 / 33 + latticeSumSaving by
          norm_num [largeSieveAlpha]
          ring]
      rw [show largeSieveAlpha + largeSieveAlpha / 3 + 2 / 3 =
        (262 / 231 : Real) by norm_num [largeSieveAlpha]]
      rw [show (2 / 3 : Real) * hybridResidualHalfDecay = 20 / 63 by
        norm_num [hybridResidualHalfDecay]]
    _ <= Q ^ (3 / 2 + latticeSumSaving) * E ^ (6 / 5 : Real) /
        X ^ (3 / 10 : Real) := by
      have hnum :
          Q ^ (49 / 33 + latticeSumSaving) * E ^ (262 / 231 : Real) <=
            Q ^ (3 / 2 + latticeSumSaving) * E ^ (6 / 5 : Real) :=
        mul_rpow_le_mul_rpow_of_exponents hQ hE (by norm_num) (by norm_num)
      have hden : X ^ (3 / 10 : Real) <= X ^ (20 / 63 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      exact div_le_div₀ (by positivity) hnum (by positivity) hden

private theorem secondTailRaw_le
    {Q E D0 D1 G X : Real}
    (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) (hX : 1 <= X) :
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) <=
      Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real) := by
  have hQPos : 0 < Q := by positivity
  have hD : 1 <= D0 * D1 := by
    calc
      (1 : Real) <= D1 := hD1
      _ = 1 * D1 := by ring
      _ <= D0 * D1 := mul_le_mul_of_nonneg_right hD0 (by positivity)
  have hXPower :
      X ^ (9 / 8 : Real) <=
        X ^ (hybridResidualHalfDecay + largeSieveSigma) :=
    Real.rpow_le_rpow_of_exponent_le hX (by
      norm_num [hybridResidualHalfDecay, largeSieveSigma])
  have hDhalf :
      (D0 * D1) ^ (1 / 2 : Real) <= D0 * D1 := by
    calc
      (D0 * D1) ^ (1 / 2 : Real) <= (D0 * D1) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
      _ = D0 * D1 := Real.rpow_one _
  have hDGRatio :
      (D0 * D1) ^ (1 / 2 : Real) / (D0 * D1 * G) <= 1 := by
    apply (div_le_one (by positivity)).2
    calc
      (D0 * D1) ^ (1 / 2 : Real) <= D0 * D1 := hDhalf
      _ <= D0 * D1 * G := by nlinarith
  have hQcombine :
      Q ^ 3 * Q ^ latticeSumSaving = Q ^ (3 + latticeSumSaving) := by
    calc
      Q ^ 3 * Q ^ latticeSumSaving =
          Q ^ (3 : Real) * Q ^ latticeSumSaving :=
        congrArg (fun z : Real => z * Q ^ latticeSumSaving)
          (Real.rpow_natCast Q 3).symm
      _ = Q ^ ((3 : Real) + latticeSumSaving) :=
        (Real.rpow_add hQPos _ _).symm
  have hXcombine :
      X ^ hybridResidualHalfDecay * X ^ largeSieveSigma =
        X ^ (hybridResidualHalfDecay + largeSieveSigma) :=
    (Real.rpow_add (show 0 < X by positivity) _ _).symm
  calc
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) =
      (Q ^ (3 + latticeSumSaving) * E ^ 2 /
        X ^ (hybridResidualHalfDecay + largeSieveSigma)) *
          ((D0 * D1) ^ (1 / 2 : Real) / (D0 * D1 * G)) := by
      field_simp
      rw [hQcombine, hXcombine]
      ring
    _ <= Q ^ (3 + latticeSumSaving) * E ^ 2 /
        X ^ (hybridResidualHalfDecay + largeSieveSigma) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hDGRatio
        (show 0 <= Q ^ (3 + latticeSumSaving) * E ^ 2 /
          X ^ (hybridResidualHalfDecay + largeSieveSigma) by positivity)
    _ <= Q ^ (3 + latticeSumSaving) * E ^ 2 /
        X ^ (9 / 8 : Real) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hXPower

private theorem secondGoodTerm_le
    {A X Q E : Real}
    (hA : 1 <= A) (hX : 1 <= X) (hQ : 1 <= Q) (hE : 1 <= E)
    (hscale : Q * E <= A * X ^ (1 - (17 / 40 : Real))) :
    Q ^ (3 / 2 + latticeSumSaving) * E ^ (6 / 5 : Real) /
        X ^ (3 / 10 : Real) <=
      A ^ (1 / 2 + latticeSumSaving + latticeSumSaving) *
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) := by
  let c : Real := 1 / 2 + latticeSumSaving + latticeSumSaving
  have hc : 0 <= c := by
    dsimp only [c]
    norm_num [latticeSumSaving]
  have hresidual :
      Q ^ (1 / 2 + latticeSumSaving + latticeSumSaving) *
          E ^ (1 / 5 + latticeSumSaving) <= (Q * E) ^ c := by
    apply mul_rpow_le_mul_rpow_product hQ hE
    · rfl
    · dsimp only [c]
      norm_num [latticeSumSaving]
  have hexponent : c * (1 - (17 / 40 : Real)) <= 3 / 10 := by
    dsimp only [c]
    norm_num [latticeSumSaving]
  have habsorb :
      (Q * E) ^ c / X ^ (3 / 10 : Real) <= A ^ c :=
    latticeScale_rpow_div_rpow_le (le_trans (by norm_num) hA) hX
      (by positivity) hc hscale hexponent
  have htarget :
      0 <= Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving) := by
    positivity
  calc
    Q ^ (3 / 2 + latticeSumSaving) * E ^ (6 / 5 : Real) /
        X ^ (3 / 10 : Real) =
      (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        (Q ^ (1 / 2 + latticeSumSaving + latticeSumSaving) *
          E ^ (1 / 5 + latticeSumSaving) / X ^ (3 / 10 : Real)) := by
      rw [show
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
            (Q ^ (1 / 2 + latticeSumSaving + latticeSumSaving) *
              E ^ (1 / 5 + latticeSumSaving) / X ^ (3 / 10 : Real)) =
          ((Q ^ (1 - latticeSumSaving) *
              Q ^ (1 / 2 + latticeSumSaving + latticeSumSaving)) *
            (E ^ (1 - latticeSumSaving) *
              E ^ (1 / 5 + latticeSumSaving))) / X ^ (3 / 10 : Real) by ring]
      rw [← Real.rpow_add (show 0 < Q by positivity),
        ← Real.rpow_add (show 0 < E by positivity)]
      rw [show (1 - latticeSumSaving) +
          (1 / 2 + latticeSumSaving + latticeSumSaving) =
        3 / 2 + latticeSumSaving by ring]
      rw [show (1 - latticeSumSaving) + (1 / 5 + latticeSumSaving) =
        (6 / 5 : Real) by ring]
    _ <= (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        ((Q * E) ^ c / X ^ (3 / 10 : Real)) := by
      apply mul_le_mul_of_nonneg_left _ htarget
      exact div_le_div_of_nonneg_right hresidual (by positivity)
    _ <= (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        A ^ c := by gcongr
    _ = A ^ c *
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) := by ring

/-- The interpolated `S2` head is absorbed by the source scale relation. -/
theorem latticeScalarSecondHeadAbsorbed_le
    {A X Q E D0 D1 G : Real}
    (hA : 1 <= A) (hX : 1 <= X) (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G)
    (hscale : Q * E <= A * X ^ (1 - (17 / 40 : Real))) :
    Q ^ latticeSumSaving *
        (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^ largeSieveAlpha *
      (((Q * E) ^ largeSieveAlpha) ^ (1 / 3 : Real) *
        (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) ^ (2 / 3 : Real)) <=
      A ^ (1 / 2 + latticeSumSaving + latticeSumSaving) *
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) := by
  exact (latticeScalarSecondHead_le hQ hE hD0 hD1 hG hX).trans
    (secondGoodTerm_le hA hX hQ hE hscale)

/-- The `S2` tail in the second branch retains the residual used in the final
weighted minimum. -/
theorem latticeScalarSecondTail_le
    {Q E D0 D1 G X : Real}
    (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) (hX : 1 <= X) :
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) <=
      Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real) :=
  secondTailRaw_le hQ hE hD0 hD1 hG hX

end

end PrimesRestrictedDigits
