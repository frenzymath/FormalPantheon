import PrimesRestrictedDigits.LatticeEstimates.FinalScalarBasic

/-!
# First dominance branch of the final lattice estimate

This file proves the two scalar comparisons used when the first term of the Alternative Hybrid
Bound dominates.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem rpow_sq_rpow
    (x exponent : Real) (hx : 0 <= x) :
    (x ^ 2) ^ exponent = x ^ (2 * exponent) := by
  calc
    (x ^ 2) ^ exponent = (x ^ (2 : Real)) ^ exponent :=
      congrArg (fun y : Real => y ^ exponent)
        (Real.rpow_natCast x 2).symm
    _ = x ^ ((2 : Real) * exponent) :=
      (Real.rpow_mul hx 2 exponent).symm

private theorem firstHeadBase_le
    {Q E D0 D1 G : Real}
    (_hQ : 0 <= Q) (_hE : 0 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) :
    (D0 * D1 * E) *
        (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) <=
      Q ^ 2 * E ^ 2 := by
  have hGSq : 1 <= G ^ 2 := by nlinarith [sq_nonneg G]
  have hden : 1 <= D1 * G ^ 2 := by
    calc
      (1 : Real) <= G ^ 2 := hGSq
      _ = 1 * G ^ 2 := by ring
      _ <= D1 * G ^ 2 :=
        mul_le_mul_of_nonneg_right hD1 (le_trans (by norm_num) hGSq)
  have hdenPos : 0 < D1 * G ^ 2 := Real.zero_lt_one.trans_le hden
  have hnum : 0 <= Q ^ 2 * E ^ 2 := by positivity
  calc
    (D0 * D1 * E) *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) =
        (Q ^ 2 * E ^ 2) / (D1 * G ^ 2) := by
      field_simp
    _ <= Q ^ 2 * E ^ 2 := by
      apply (div_le_iff₀ hdenPos).2
      nlinarith [mul_nonneg hnum (sub_nonneg.mpr hden)]

/-- The first head product is coordinatewise below the final saved powers. -/
theorem latticeScalarFirstHead_le
    {Q E D0 D1 G : Real}
    (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G) :
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^
            largeSieveAlpha) <=
      Q ^ (1 - latticeSumSaving) *
        E ^ (1 - latticeSumSaving) := by
  have hQPos : 0 < Q := Real.zero_lt_one.trans_le hQ
  have hEPos : 0 < E := Real.zero_lt_one.trans_le hE
  have hleftBase : 0 <= D0 * D1 * E := by positivity
  have hrightBase : 0 <= Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2) := by
    positivity
  have hbase := firstHeadBase_le hQPos.le hEPos.le hD0 hD1 hG
  have hbasePower :
      ((D0 * D1 * E) *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2))) ^
          largeSieveAlpha <=
        (Q ^ 2 * E ^ 2) ^ largeSieveAlpha :=
    Real.rpow_le_rpow (mul_nonneg hleftBase hrightBase) hbase
      largeSieveAlpha_nonneg
  have hcombined :
      (D0 * D1 * E) ^ largeSieveAlpha *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^
            largeSieveAlpha <=
        Q ^ (2 * largeSieveAlpha) *
          E ^ (2 * largeSieveAlpha) := by
    calc
      (D0 * D1 * E) ^ largeSieveAlpha *
            (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^
              largeSieveAlpha =
          ((D0 * D1 * E) *
            (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2))) ^
              largeSieveAlpha :=
        (Real.mul_rpow hleftBase hrightBase).symm
      _ <= (Q ^ 2 * E ^ 2) ^ largeSieveAlpha := hbasePower
      _ = (Q ^ 2) ^ largeSieveAlpha *
          (E ^ 2) ^ largeSieveAlpha := by
        rw [Real.mul_rpow (sq_nonneg Q) (sq_nonneg E)]
      _ = Q ^ (2 * largeSieveAlpha) *
          E ^ (2 * largeSieveAlpha) := by
        rw [rpow_sq_rpow Q largeSieveAlpha hQPos.le,
          rpow_sq_rpow E largeSieveAlpha hEPos.le]
  have hQExponent :
      hybridResidualGrowth + latticeSumSaving +
          2 * largeSieveAlpha <= 1 - latticeSumSaving := by
    norm_num [hybridResidualGrowth, largeSieveAlpha, latticeSumSaving]
  have hEExponent :
      2 * largeSieveAlpha <= 1 - latticeSumSaving := by
    norm_num [largeSieveAlpha, latticeSumSaving]
  calc
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^
            largeSieveAlpha) =
      (Q ^ hybridResidualGrowth * Q ^ latticeSumSaving) *
        ((D0 * D1 * E) ^ largeSieveAlpha *
          (Q ^ 2 * E / (D0 * D1 ^ 2 * G ^ 2)) ^
            largeSieveAlpha) := by ring
    _ <= (Q ^ hybridResidualGrowth * Q ^ latticeSumSaving) *
        (Q ^ (2 * largeSieveAlpha) *
          E ^ (2 * largeSieveAlpha)) := by gcongr
    _ = Q ^ (hybridResidualGrowth + latticeSumSaving +
          2 * largeSieveAlpha) * E ^ (2 * largeSieveAlpha) := by
      rw [← Real.rpow_add hQPos]
      calc
        Q ^ (hybridResidualGrowth + latticeSumSaving) *
              (Q ^ (2 * largeSieveAlpha) *
                E ^ (2 * largeSieveAlpha)) =
            (Q ^ (hybridResidualGrowth + latticeSumSaving) *
              Q ^ (2 * largeSieveAlpha)) *
                E ^ (2 * largeSieveAlpha) := by ring
        _ = Q ^ (hybridResidualGrowth + latticeSumSaving +
              2 * largeSieveAlpha) * E ^ (2 * largeSieveAlpha) := by
          rw [← Real.rpow_add hQPos]
    _ <= Q ^ (1 - latticeSumSaving) *
        E ^ (1 - latticeSumSaving) :=
      mul_rpow_le_mul_rpow_of_exponents hQ hE hQExponent hEExponent

private theorem firstTailRaw_le
    {Q E D0 D1 G X : Real}
    (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G)
    (hX : 0 < X) :
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) <=
      Q ^ (2 + hybridResidualGrowth + latticeSumSaving) * E ^ 2 /
        X ^ largeSieveSigma := by
  have hQPos : 0 < Q := Real.zero_lt_one.trans_le hQ
  have hD01 : 1 <= D0 * D1 := by
    calc
      (1 : Real) <= D1 := hD1
      _ = 1 * D1 := by ring
      _ <= D0 * D1 :=
        mul_le_mul_of_nonneg_right hD0 (le_trans (by norm_num) hD1)
  have hDE : 1 <= D0 * D1 * E := by
    calc
      (1 : Real) <= E := hE
      _ = 1 * E := by ring
      _ <= (D0 * D1) * E :=
        mul_le_mul_of_nonneg_right hD01 (le_trans (by norm_num) hE)
  have hDEPower :
      (D0 * D1 * E) ^ largeSieveAlpha <= D0 * D1 * E := by
    calc
      (D0 * D1 * E) ^ largeSieveAlpha <=
          (D0 * D1 * E) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hDE (by
          norm_num [largeSieveAlpha])
      _ = D0 * D1 * E := Real.rpow_one _
  have hdenPos : 0 < D0 * D1 * G := by positivity
  have hratio :
      (D0 * D1 * E) ^ largeSieveAlpha /
          (D0 * D1 * G) <= E := by
    apply (div_le_iff₀ hdenPos).2
    calc
      (D0 * D1 * E) ^ largeSieveAlpha <= D0 * D1 * E := hDEPower
      _ <= E * (D0 * D1 * G) := by
        have hG' : D0 * D1 <= D0 * D1 * G := by nlinarith
        calc
          D0 * D1 * E = E * (D0 * D1) := by ring
          _ <= E * (D0 * D1 * G) :=
            mul_le_mul_of_nonneg_left hG' (by positivity)
  have hXPowerPos : 0 < X ^ largeSieveSigma :=
    Real.rpow_pos_of_pos hX _
  calc
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) =
      (Q ^ hybridResidualGrowth * Q ^ latticeSumSaving * Q ^ 2 * E) *
        ((D0 * D1 * E) ^ largeSieveAlpha /
          (D0 * D1 * G)) / X ^ largeSieveSigma := by
      field_simp
    _ <= (Q ^ hybridResidualGrowth * Q ^ latticeSumSaving * Q ^ 2 * E) *
        E / X ^ largeSieveSigma := by gcongr
    _ = Q ^ (2 + hybridResidualGrowth + latticeSumSaving) * E ^ 2 /
        X ^ largeSieveSigma := by
      have hQcombine :
          Q ^ hybridResidualGrowth * Q ^ latticeSumSaving * Q ^ 2 =
            Q ^ (2 + hybridResidualGrowth + latticeSumSaving) := by
        rw [← Real.rpow_add hQPos, show Q ^ 2 = Q ^ (2 : Real) by
          exact (Real.rpow_natCast Q 2).symm]
        rw [← Real.rpow_add hQPos]
        congr 1
        ring
      rw [hQcombine]
      ring

/-- The first tail product is absorbed by the source scale relation. -/
theorem latticeScalarFirstTail_le
    {A X Q E D0 D1 G : Real}
    (hA : 1 <= A) (hX : 1 <= X) (hQ : 1 <= Q) (hE : 1 <= E)
    (hD0 : 1 <= D0) (hD1 : 1 <= D1) (hG : 1 <= G)
    (hscale : Q * E <= A * X ^ (1 - (17 / 40 : Real))) :
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) <=
      A ^ (1 + hybridResidualGrowth + latticeSumSaving +
          latticeSumSaving) *
        (Q ^ (1 - latticeSumSaving) *
          E ^ (1 - latticeSumSaving)) := by
  let c : Real := 1 + hybridResidualGrowth + latticeSumSaving +
    latticeSumSaving
  have hraw := firstTailRaw_le hQ hE hD0 hD1 hG
    (Real.zero_lt_one.trans_le hX)
  have hc : 0 <= c := by
    dsimp only [c]
    norm_num [hybridResidualGrowth, latticeSumSaving]
  have hresidual :
      Q ^ (1 + hybridResidualGrowth + latticeSumSaving +
          latticeSumSaving) * E ^ (1 + latticeSumSaving) <=
        (Q * E) ^ c := by
    apply mul_rpow_le_mul_rpow_product hQ hE
    · rfl
    · dsimp only [c]
      have hgrowth : 0 <= hybridResidualGrowth := by
        norm_num [hybridResidualGrowth]
      have hsaving : 0 <= latticeSumSaving := latticeSumSaving_pos.le
      linarith
  have hexponent : c * (1 - (17 / 40 : Real)) <= largeSieveSigma := by
    dsimp only [c]
    norm_num [hybridResidualGrowth, largeSieveSigma, latticeSumSaving]
  have habsorb :
      (Q * E) ^ c / X ^ largeSieveSigma <= A ^ c :=
    latticeScale_rpow_div_rpow_le (le_trans (by norm_num) hA) hX
      (by positivity) hc hscale hexponent
  have htargetNonneg :
      0 <= Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving) := by
    positivity
  calc
    (Q ^ hybridResidualGrowth *
          (D0 * D1 * E) ^ largeSieveAlpha) *
        (Q ^ latticeSumSaving *
          (Q ^ 2 * E /
            (D0 * D1 * G * X ^ largeSieveSigma))) <=
      Q ^ (2 + hybridResidualGrowth + latticeSumSaving) * E ^ 2 /
        X ^ largeSieveSigma := hraw
    _ = (Q ^ (1 - latticeSumSaving) *
          E ^ (1 - latticeSumSaving)) *
        (Q ^ (1 + hybridResidualGrowth + latticeSumSaving +
            latticeSumSaving) * E ^ (1 + latticeSumSaving) /
          X ^ largeSieveSigma) := by
      have hQPos : 0 < Q := by positivity
      have hEPos : 0 < E := by positivity
      rw [show
        (Q ^ (1 - latticeSumSaving) * E ^ (1 - latticeSumSaving)) *
            (Q ^ (1 + hybridResidualGrowth + latticeSumSaving +
                latticeSumSaving) * E ^ (1 + latticeSumSaving) /
              X ^ largeSieveSigma) =
          ((Q ^ (1 - latticeSumSaving) *
              Q ^ (1 + hybridResidualGrowth + latticeSumSaving +
                latticeSumSaving)) *
            (E ^ (1 - latticeSumSaving) *
              E ^ (1 + latticeSumSaving))) /
                X ^ largeSieveSigma by ring]
      rw [← Real.rpow_add hQPos, ← Real.rpow_add hEPos]
      rw [show
        (1 - latticeSumSaving) +
            (1 + hybridResidualGrowth + latticeSumSaving +
              latticeSumSaving) =
          2 + hybridResidualGrowth + latticeSumSaving by ring]
      rw [show
        (1 - latticeSumSaving) + (1 + latticeSumSaving) =
          (2 : Real) by ring]
      exact congrArg
        (fun z : Real =>
          Q ^ (2 + hybridResidualGrowth + latticeSumSaving) * z /
            X ^ largeSieveSigma)
        (Real.rpow_natCast E 2).symm
    _ <= (Q ^ (1 - latticeSumSaving) *
          E ^ (1 - latticeSumSaving)) *
        ((Q * E) ^ c / X ^ largeSieveSigma) := by
      apply mul_le_mul_of_nonneg_left _ htargetNonneg
      exact div_le_div_of_nonneg_right hresidual (by positivity)
    _ <= (Q ^ (1 - latticeSumSaving) *
          E ^ (1 - latticeSumSaving)) * A ^ c := by gcongr
    _ = A ^ c *
        (Q ^ (1 - latticeSumSaving) *
          E ^ (1 - latticeSumSaving)) := by ring

end

end PrimesRestrictedDigits
