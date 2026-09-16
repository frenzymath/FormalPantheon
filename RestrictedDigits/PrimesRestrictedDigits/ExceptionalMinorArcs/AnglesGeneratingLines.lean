import PrimesRestrictedDigits.ExceptionalMinorArcs.AnglesGeneratingLinesBandBounds

/-!
# Bound for angles generating lines

The decimal padded-scale form of `MAYNARD-PRD-PUBLISHED`, Proposition 13.4,
including the factor-ten loss and the range where the height is below one.
-/

namespace PrimesRestrictedDigits

/-- Quantitative coefficient-one form of Proposition 13.4 for every saving
strictly below the exact trivial-branch margin. -/
theorem exists_lineGeneratingComparableBand_sum_le
    (eta : Real) (heta : 0 < eta)
    (hetaMax : eta < anglesGeneratingLinesSavingLimit) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (digit : Fin 10) (N K delta B : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        X ^ (9 / 25 : Real) <= N ->
        1 <= K ->
        N <= delta * X ->
        1 <= B ->
        B <= X ^ (23 / 80 : Real) ->
        lineGeneratingBandWeightSum digit length B delta N K <=
          X ^ (1 - eta) / (N * K) := by
  obtain ⟨lengthPairs, hpairs⟩ :=
    exists_card_lineGeneratingPairs_le_threshold eta heta
  obtain ⟨lengthCoeff, hcoeff⟩ :=
    exists_anglesGeneratingLinesCoefficientThreshold eta heta hetaMax
  refine ⟨max lengthPairs lengthCoeff, ?_⟩
  intro length hlength digit N K delta B
  dsimp only
  intro hNlower hK hwidth hB hBupper
  let X : Real := ((10 ^ length : Nat) : Real)
  let C := comparableMagnitudeFrequencies digit length B
  let H : Real := (C.card : Real)
  let W : Real := lineGeneratingBandWeightSum digit length B delta N K
  let Q : Real := N * K
  let R : Real := X / Q
  let V : Real := 4 * X / (N ^ 2 * K)
  change W <= X ^ (1 - eta) / Q
  have hlengthPairs : lengthPairs <= length := by omega
  have hlengthCoeff : lengthCoeff <= length := by omega
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  have hXOne : 1 <= X := by
    dsimp only [X]
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hN : 0 < N :=
    (Real.rpow_pos_of_pos hX (9 / 25 : Real)).trans_le hNlower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hH : 0 <= H := by
    dsimp only [H]
    positivity
  have hHbound : H <=
      (10 * B) ^ (235 / 154 : Real) * X ^ (59 / 433 : Real) := by
    simpa only [H, C, X] using
      card_comparableMagnitudeFrequencies_le digit length B hBpos
  have hcoeffAtLength := hcoeff length hlengthCoeff
  have hcoeffTrivial :
      (10 : Real) ^ (2 * (235 / 154 : Real)) <=
        X ^ (anglesGeneratingLinesSavingLimit - eta) := by
    simpa only [X] using hcoeffAtLength.1
  have hcoeffLine :
      16 * (10 : Real) ^
            ((235 / 154 : Real) * (5 / 4 : Real)) +
          64 * (10 : Real) ^
            ((235 / 154 : Real) * (3 / 2 : Real)) <=
        X ^ (anglesGeneratingLinesFirstSaving - 2 * eta) := by
    simpa only [X, mul_comm] using hcoeffAtLength.2
  by_cases hsmall : Q <= X ^ (57 / 80 : Real) / B
  · have hWambient : W <= H ^ 2 / B ^ 2 := by
      simpa only [W, H, C] using
        lineGeneratingBandWeightSum_le_ambient_sq_div
          digit length B delta N K hBpos
    have htrivial : W * Q <=
        10 ^ (2 * (235 / 154 : Real)) *
          X ^ (1 - anglesGeneratingLinesSavingLimit) :=
      anglesGeneratingLines_trivial_band_bound X B H W Q hX hBpos
        hBupper hH hHbound hWambient hQ.le hsmall
    apply (le_div_iff₀ hQ).2
    calc
      W * Q <= 10 ^ (2 * (235 / 154 : Real)) *
          X ^ (1 - anglesGeneratingLinesSavingLimit) := htrivial
      _ <= X ^ (anglesGeneratingLinesSavingLimit - eta) *
          X ^ (1 - anglesGeneratingLinesSavingLimit) := by
        exact mul_le_mul_of_nonneg_right hcoeffTrivial
          (Real.rpow_nonneg hX.le _)
      _ = X ^ (1 - eta) := by
        rw [← Real.rpow_add hX]
        congr 1
        ring
  · have hlarge : X ^ (57 / 80 : Real) / B < Q :=
      lt_of_not_ge hsmall
    have hlarge' : X ^ (57 / 80 : Real) < Q * B :=
      (div_lt_iff₀ hBpos).mp hlarge
    have hRupper : R <= B * X ^ (23 / 80 : Real) := by
      have hmul := mul_lt_mul_of_pos_right hlarge'
        (Real.rpow_pos_of_pos hX (23 / 80 : Real))
      have hpower :
          X ^ (57 / 80 : Real) * X ^ (23 / 80 : Real) = X := by
        calc
          X ^ (57 / 80 : Real) * X ^ (23 / 80 : Real) =
              X ^ ((57 / 80 : Real) + 23 / 80) :=
            (Real.rpow_add hX _ _).symm
          _ = X := by norm_num
      apply (div_le_iff₀ hQ).2
      rw [hpower] at hmul
      nlinarith
    have hfirst := anglesGeneratingLines_first_band_factor_bound
      X B H R hX hBpos hBupper hH hHbound hR.le hRupper
    have hsecond := anglesGeneratingLines_second_band_factor_bound
      X B H R hX hBpos hBupper hH hHbound hR.le hRupper
    have hfirstN := anglesGeneratingLines_first_N_factor_bound
      X N hX hNlower
    have hsecondN := anglesGeneratingLines_second_N_factor_bound
      X N hX hNlower
    have hcard :
        ((lineGeneratingPairs C delta N K).card : Real) <=
          X ^ eta *
            (H ^ (5 / 4 : Real) * V ^ 2 +
              H ^ (3 / 2 : Real) * V ^ 3 /
                X ^ (1 / 2 : Real)) := by
      simpa only [C, H, V, X] using
        hpairs length hlengthPairs C delta N K hNlower hK hwidth
    have hWcard : W <=
        ((lineGeneratingPairs C delta N K).card : Real) / B ^ 2 := by
      simpa only [W, C] using
        lineGeneratingBandWeightSum_le_card_div_sq
          digit length B delta N K hBpos
    have hWraw : W <=
        (X ^ eta *
          (H ^ (5 / 4 : Real) * V ^ 2 +
            H ^ (3 / 2 : Real) * V ^ 3 /
              X ^ (1 / 2 : Real))) / B ^ 2 :=
      hWcard.trans ((div_le_div_iff_of_pos_right (sq_pos_of_pos hBpos)).2 hcard)
    have hshape :
        (X ^ eta *
          (H ^ (5 / 4 : Real) * V ^ 2 +
            H ^ (3 / 2 : Real) * V ^ 3 /
              X ^ (1 / 2 : Real))) / B ^ 2 =
        X ^ eta * R *
          (16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 *
              (H ^ (3 / 2 : Real) / B ^ 2 /
                X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3) := by
      dsimp only [V, R, Q]
      field_simp
      ring
    have hfirstTerm :
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 <=
          16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            X ^ (-anglesGeneratingLinesFirstSaving) := by
      calc
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 <=
            16 *
              (10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
                X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real)) /
                  N ^ 2 := by gcongr
        _ = 16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            (X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) /
              N ^ 2) := by ring
        _ <= 16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            X ^ (-anglesGeneratingLinesFirstSaving) := by gcongr
    have hsecondTerm :
        64 * (H ^ (3 / 2 : Real) / B ^ 2 /
            X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
          64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            X ^ (-anglesGeneratingLinesSecondSaving) := by
      calc
        64 * (H ^ (3 / 2 : Real) / B ^ 2 /
            X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
            64 *
              (10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
                X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real)) /
                  N ^ 3 := by gcongr
        _ = 64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            (X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) /
              N ^ 3) := by ring
        _ <= 64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            X ^ (-anglesGeneratingLinesSecondSaving) := by gcongr
    have hsecondPower :
        X ^ (-anglesGeneratingLinesSecondSaving) <=
          X ^ (-anglesGeneratingLinesFirstSaving) :=
      Real.rpow_le_rpow_of_exponent_le hXOne
        (neg_le_neg
          anglesGeneratingLines_secondSaving_gt_firstSaving.le)
    have hinner :
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 * (H ^ (3 / 2 : Real) / B ^ 2 /
              X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
          (16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) +
            64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real))) *
              X ^ (-anglesGeneratingLinesFirstSaving) := by
      calc
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 * (H ^ (3 / 2 : Real) / B ^ 2 /
              X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
            16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
                X ^ (-anglesGeneratingLinesFirstSaving) +
              64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
                X ^ (-anglesGeneratingLinesSecondSaving) :=
          add_le_add hfirstTerm hsecondTerm
        _ <= 16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
                X ^ (-anglesGeneratingLinesFirstSaving) +
              64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
                X ^ (-anglesGeneratingLinesFirstSaving) := by gcongr
        _ = (16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) +
              64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real))) *
            X ^ (-anglesGeneratingLinesFirstSaving) := by ring
    have hinnerFinal :
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 * (H ^ (3 / 2 : Real) / B ^ 2 /
              X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
          X ^ (-2 * eta) := by
      calc
        16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 * (H ^ (3 / 2 : Real) / B ^ 2 /
              X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3 <=
            (16 * 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) +
              64 * 10 ^ ((235 / 154 : Real) * (3 / 2 : Real))) *
                X ^ (-anglesGeneratingLinesFirstSaving) := hinner
        _ <= X ^ (anglesGeneratingLinesFirstSaving - 2 * eta) *
            X ^ (-anglesGeneratingLinesFirstSaving) := by
          exact mul_le_mul_of_nonneg_right hcoeffLine
            (Real.rpow_nonneg hX.le _)
        _ = X ^ (-2 * eta) := by
          rw [← Real.rpow_add hX]
          congr 1
          ring
    calc
      W <= (X ^ eta *
          (H ^ (5 / 4 : Real) * V ^ 2 +
            H ^ (3 / 2 : Real) * V ^ 3 /
              X ^ (1 / 2 : Real))) / B ^ 2 := hWraw
      _ = X ^ eta * R *
          (16 * (H ^ (5 / 4 : Real) / B ^ 2 * R) / N ^ 2 +
            64 * (H ^ (3 / 2 : Real) / B ^ 2 /
              X ^ (1 / 2 : Real) * R ^ 2) / N ^ 3) := hshape
      _ <= X ^ eta * R * X ^ (-2 * eta) := by gcongr
      _ = X ^ (1 - eta) / Q := by
        dsimp only [R]
        calc
          X ^ eta * (X / Q) * X ^ (-2 * eta) =
              (X ^ eta * X * X ^ (-2 * eta)) / Q := by ring
          _ = (X ^ eta * X ^ (1 : Real) * X ^ (-2 * eta)) / Q := by
            rw [Real.rpow_one]
          _ = X ^ (eta + 1 + (-2 * eta)) / Q := by
            rw [← Real.rpow_add hX]
            rw [← Real.rpow_add hX]
          _ = X ^ (1 - eta) / Q := by congr 2; ring

/-- Source-facing Proposition 13.4 with the common explicit minor-arc
saving. -/
theorem exists_anglesGeneratingLinesBoundThreshold :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (digit : Fin 10) (N K delta B : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        X ^ (9 / 25 : Real) <= N ->
        1 <= K ->
        N <= delta * X ->
        1 <= B ->
        B <= X ^ (23 / 80 : Real) ->
        lineGeneratingBandWeightSum digit length B delta N K <=
          X ^ (1 - anglesGeneratingLinesSaving) / (N * K) := by
  exact exists_lineGeneratingComparableBand_sum_le
    anglesGeneratingLinesSaving anglesGeneratingLinesSaving_pos
      anglesGeneratingLinesSaving_lt_limit

end PrimesRestrictedDigits
