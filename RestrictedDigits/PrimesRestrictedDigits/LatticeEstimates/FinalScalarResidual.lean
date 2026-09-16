import PrimesRestrictedDigits.LatticeEstimates.FinalScalarSecond

/-!
# Residual terms in the final lattice estimate

This file absorbs the second `S1*S3` term and proves the corrected weighted minimum of the two
residual terms in published Lemma 14.4.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem sThreeCrossRaw_le
    {X Q E D0 D1 P : Real}
    (hX : 1 <= X) (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hP : 1 <= P) :
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) <=
      Q ^ 2 * E / (P * X ^ (3 / 16 : Real)) := by
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hD : 1 <= D0 * D1 := by
    calc
      (1 : Real) <= D1 := hD1
      _ = 1 * D1 := by ring
      _ <= D0 * D1 := mul_le_mul_of_nonneg_right hD0 (by positivity)
  have hDhalf :
      (D0 * D1) ^ (1 / 2 : Real) <= D0 * D1 := by
    calc
      (D0 * D1) ^ (1 / 2 : Real) <= (D0 * D1) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
      _ = D0 * D1 := Real.rpow_one _
  have hDratio :
      (D0 * D1) ^ (1 / 2 : Real) / (D0 * D1) <= 1 :=
    (div_le_one (by positivity)).2 hDhalf
  have hdecayGap :
      (3 / 16 : Real) <= hybridResidualHalfDecay - 23 / 80 := by
    norm_num [hybridResidualHalfDecay]
  have hXPower :
      X ^ (3 / 16 : Real) <=
        X ^ (hybridResidualHalfDecay - 23 / 80) :=
    Real.rpow_le_rpow_of_exponent_le hX hdecayGap
  have hXratio :
      X ^ (23 / 80 : Real) / X ^ hybridResidualHalfDecay <=
        1 / X ^ (3 / 16 : Real) := by
    calc
      X ^ (23 / 80 : Real) / X ^ hybridResidualHalfDecay =
          X ^ ((23 / 80 : Real) - hybridResidualHalfDecay) :=
        (Real.rpow_sub hXPos _ _).symm
      _ = 1 / X ^ (hybridResidualHalfDecay - 23 / 80) := by
        rw [show (23 / 80 : Real) - hybridResidualHalfDecay =
          -(hybridResidualHalfDecay - 23 / 80) by ring]
        rw [Real.rpow_neg hXPos.le]
        rw [one_div]
      _ <= 1 / X ^ (3 / 16 : Real) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hXPower
  have hcoreNonneg : 0 <= Q ^ 2 * E / P := by positivity
  calc
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) =
      (Q ^ 2 * E / P) *
        ((D0 * D1) ^ (1 / 2 : Real) / (D0 * D1)) *
          (X ^ (23 / 80 : Real) / X ^ hybridResidualHalfDecay) := by
      field_simp
    _ <= (Q ^ 2 * E / P) * 1 *
        (1 / X ^ (3 / 16 : Real)) := by gcongr
    _ = Q ^ 2 * E / (P * X ^ (3 / 16 : Real)) := by ring

/-- The second `S1*S3` term is a fixed multiple of the final saved powers. -/
theorem latticeScalarSThreeCross_le
    {A X P Q E D0 D1 : Real}
    (hA : 1 <= A) (hX : 1 <= X) (hP : 1 <= P)
    (hQ : 1 <= Q) (hE : 1 <= E) (hD0 : 1 <= D0) (hD1 : 1 <= D1)
    (hPscale : X ^ (17 / 40 : Real) <= P)
    (hscale : Q * E <= A * X ^ (1 - (17 / 40 : Real))) :
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) <=
      A ^ (1 + latticeSumSaving) *
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) := by
  let c : Real := 1 + latticeSumSaving
  have hc : 0 <= c := by
    dsimp only [c]
    norm_num [latticeSumSaving]
  have hraw := sThreeCrossRaw_le hX hQ hE hD0 hD1 hP
  have hresidual :
      Q ^ (1 + latticeSumSaving) * E ^ latticeSumSaving <=
        (Q * E) ^ c := by
    apply mul_rpow_le_mul_rpow_product hQ hE
    · rfl
    · dsimp only [c]
      norm_num [latticeSumSaving]
  have hdenScale :
      X ^ ((17 / 40 : Real) + 3 / 16) <=
        P * X ^ (3 / 16 : Real) := by
    calc
      X ^ ((17 / 40 : Real) + 3 / 16) =
          X ^ (17 / 40 : Real) * X ^ (3 / 16 : Real) :=
        Real.rpow_add (Real.zero_lt_one.trans_le hX) _ _
      _ <= P * X ^ (3 / 16 : Real) :=
        mul_le_mul_of_nonneg_right hPscale (by positivity)
  have hexponent :
      c * (1 - (17 / 40 : Real)) <= (17 / 40 : Real) + 3 / 16 := by
    dsimp only [c]
    norm_num [latticeSumSaving]
  have habsorb :
      (Q * E) ^ c / X ^ ((17 / 40 : Real) + 3 / 16) <= A ^ c :=
    latticeScale_rpow_div_rpow_le (le_trans (by norm_num) hA) hX
      (by positivity) hc hscale hexponent
  have htarget :
      0 <= Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving) := by
    positivity
  calc
    (Q * E * (D0 * D1) ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) *
        (Q * X ^ (23 / 80 : Real) / (D0 * D1 * P)) <=
      Q ^ 2 * E / (P * X ^ (3 / 16 : Real)) := hraw
    _ = (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        (Q ^ (1 + latticeSumSaving) * E ^ latticeSumSaving /
          (P * X ^ (3 / 16 : Real))) := by
      rw [show
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
            (Q ^ (1 + latticeSumSaving) * E ^ latticeSumSaving /
              (P * X ^ (3 / 16 : Real))) =
          ((Q ^ (1 - latticeSumSaving) * Q ^ (1 + latticeSumSaving)) *
            (E ^ (1 - latticeSumSaving) * E ^ latticeSumSaving)) /
              (P * X ^ (3 / 16 : Real)) by ring]
      rw [← Real.rpow_add (show 0 < Q by positivity),
        ← Real.rpow_add (show 0 < E by positivity)]
      rw [show (1 - latticeSumSaving) + (1 + latticeSumSaving) =
        (2 : Real) by ring]
      rw [show (1 - latticeSumSaving) + latticeSumSaving =
        (1 : Real) by ring, Real.rpow_one]
      exact congrArg
        (fun z : Real => z * E / (P * X ^ (3 / 16 : Real)))
        (Real.rpow_natCast Q 2).symm
    _ <= (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        ((Q * E) ^ c / (P * X ^ (3 / 16 : Real))) := by
      apply mul_le_mul_of_nonneg_left _ htarget
      exact div_le_div_of_nonneg_right hresidual (by positivity)
    _ <= (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        ((Q * E) ^ c / X ^ ((17 / 40 : Real) + 3 / 16)) := by
      apply mul_le_mul_of_nonneg_left _ htarget
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdenScale
    _ <= (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
        A ^ c := by gcongr
    _ = A ^ c *
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) := by ring

private theorem firstResidualPower_eq
    {X Q E : Real} (hX : 0 < X) (hQ : 0 <= Q) (hE : 0 <= E) :
    (X ^ (23 / 80 : Real) * (Q * E) ^ largeSieveAlpha) ^
        (77 / 100 : Real) =
      X ^ ((23 / 80 : Real) * (77 / 100)) *
        (Q ^ (largeSieveAlpha * (77 / 100)) *
          E ^ (largeSieveAlpha * (77 / 100))) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg (by positivity) _)]
  rw [rpow_rpow_eq_mul hX.le]
  rw [Real.mul_rpow hQ hE]
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hE _)]
  rw [rpow_rpow_eq_mul hQ, rpow_rpow_eq_mul hE]

private theorem secondResidualPower_eq
    {X Q E : Real} (hX : 0 < X) (hQ : 0 <= Q) (hE : 0 <= E) :
    (Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real)) ^
        (23 / 100 : Real) =
      (Q ^ ((3 + latticeSumSaving) * (23 / 100)) *
        E ^ ((2 : Real) * (23 / 100))) /
          X ^ ((9 / 8 : Real) * (23 / 100)) := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (sq_nonneg E)]
  rw [rpow_rpow_eq_mul hQ]
  rw [pow_two_rpow E (23 / 100 : Real) hE]
  rw [rpow_rpow_eq_mul hX.le]

/-- The corrected residual minimum is below the final saved powers. -/
theorem latticeScalarResidualMinimum_le
    {X Q E : Real} (hX : 1 <= X) (hQ : 1 <= Q) (hE : 1 <= E) :
    min
        (X ^ (23 / 80 : Real) * (Q * E) ^ largeSieveAlpha)
        (Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real)) <=
      Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving) := by
  let first := X ^ (23 / 80 : Real) * (Q * E) ^ largeSieveAlpha
  let second := Q ^ (3 + latticeSumSaving) * E ^ 2 / X ^ (9 / 8 : Real)
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hQPos : 0 < Q := Real.zero_lt_one.trans_le hQ
  have hEPos : 0 < E := Real.zero_lt_one.trans_le hE
  have hweighted : min first second <=
      first ^ (77 / 100 : Real) * second ^ (23 / 100 : Real) :=
    min_le_rpow_mul_rpow (by dsimp only [first]; positivity)
      (by dsimp only [second]; positivity) (by norm_num) (by norm_num) (by norm_num)
  have heq :
      first ^ (77 / 100 : Real) * second ^ (23 / 100 : Real) =
        Q ^ (24 / 25 + (23 / 100) * latticeSumSaving) *
          E ^ (73 / 100 : Real) / X ^ (299 / 8000 : Real) := by
    dsimp only [first, second]
    rw [firstResidualPower_eq hXPos hQPos.le hEPos.le]
    rw [secondResidualPower_eq hXPos hQPos.le hEPos.le]
    rw [show
      (X ^ ((23 / 80 : Real) * (77 / 100)) *
          (Q ^ (largeSieveAlpha * (77 / 100)) *
            E ^ (largeSieveAlpha * (77 / 100)))) *
        ((Q ^ ((3 + latticeSumSaving) * (23 / 100)) *
          E ^ ((2 : Real) * (23 / 100))) /
            X ^ ((9 / 8 : Real) * (23 / 100))) =
      ((Q ^ (largeSieveAlpha * (77 / 100)) *
          Q ^ ((3 + latticeSumSaving) * (23 / 100))) *
        (E ^ (largeSieveAlpha * (77 / 100)) *
          E ^ ((2 : Real) * (23 / 100)))) /
        (X ^ ((9 / 8 : Real) * (23 / 100)) /
          X ^ ((23 / 80 : Real) * (77 / 100))) by field_simp]
    rw [← Real.rpow_add hQPos, ← Real.rpow_add hEPos]
    rw [← Real.rpow_sub hXPos]
    rw [show largeSieveAlpha * (77 / 100) +
          (3 + latticeSumSaving) * (23 / 100) =
        24 / 25 + (23 / 100) * latticeSumSaving by
          norm_num [largeSieveAlpha]
          ring]
    rw [show largeSieveAlpha * (77 / 100) +
        (2 : Real) * (23 / 100) = 73 / 100 by
      norm_num [largeSieveAlpha]]
    rw [show (9 / 8 : Real) * (23 / 100) -
        (23 / 80) * (77 / 100) = 299 / 8000 by norm_num]
  have hXdrop :
      Q ^ (24 / 25 + (23 / 100) * latticeSumSaving) *
          E ^ (73 / 100 : Real) / X ^ (299 / 8000 : Real) <=
        Q ^ (24 / 25 + (23 / 100) * latticeSumSaving) *
          E ^ (73 / 100 : Real) :=
    div_le_self (by positivity) (by
      calc
        (1 : Real) = 1 ^ (299 / 8000 : Real) := by rw [Real.one_rpow]
        _ <= X ^ (299 / 8000 : Real) :=
          Real.rpow_le_rpow (by norm_num) hX (by norm_num))
  have hQExponent :
      24 / 25 + (23 / 100) * latticeSumSaving <=
        1 - latticeSumSaving := by norm_num [latticeSumSaving]
  have hEExponent : (73 / 100 : Real) <= 1 - latticeSumSaving := by
    norm_num [latticeSumSaving]
  change min first second <= _
  calc
    min first second <= first ^ (77 / 100 : Real) *
        second ^ (23 / 100 : Real) := hweighted
    _ = Q ^ (24 / 25 + (23 / 100) * latticeSumSaving) *
          E ^ (73 / 100 : Real) / X ^ (299 / 8000 : Real) := heq
    _ <= Q ^ (24 / 25 + (23 / 100) * latticeSumSaving) *
          E ^ (73 / 100 : Real) := hXdrop
    _ <= Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving) :=
      mul_rpow_le_mul_rpow_of_exponents hQ hE hQExponent hEExponent

end

end PrimesRestrictedDigits
