import PrimesRestrictedDigits.Fourier.HybridAlignedSourceFactorization
import PrimesRestrictedDigits.Fourier.HybridDenominatorPowerBalance

/-!
# First Alternative Hybrid Bound

This file completes the first source-band conclusion of `MAYNARD-PRD-PUBLISHED`, Lemma 10.7,
pp. 180--185. It composes the separate Sigma-one and squared-block estimates and performs the
final published power conversion.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem hybridPublishedTail_eq
    {D E L Y : Real} (hD : 0 < D) (hE : 0 < E) (hY : 0 < Y) :
    E ^ largeSieveAlpha * D * L *
        (Y / (D * E)) ^ (-hybridResidualHalfDecay) =
      E ^ (largeSieveAlpha + hybridResidualHalfDecay) *
        D ^ (1 + hybridResidualHalfDecay) * L /
          Y ^ hybridResidualHalfDecay := by
  rw [Real.rpow_neg (div_nonneg hY.le (mul_nonneg hD.le hE.le))]
  rw [Real.div_rpow hY.le (mul_nonneg hD.le hE.le)]
  rw [inv_div]
  rw [Real.mul_rpow hD.le hE.le]
  rw [Real.rpow_add hE, Real.rpow_add hD, Real.rpow_one]
  ring

/-- The final scalar conversion in the first conclusion of published Lemma
10.7. The lower bounds on `D` and `E` are essential for increasing the two
tail exponents. -/
theorem hybridCommonSourceBranch_le_publishedPowers
    {d D E L Y : Real}
    (hd : 0 <= d) (hdD : d <= D)
    (hD : 1 <= D) (hE : 1 <= E)
    (hL : 0 <= L) (hY : 0 < Y) :
    E ^ largeSieveAlpha *
        (d ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          d * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) <=
      (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
        E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          Y ^ hybridResidualHalfDecay := by
  have hDPos : 0 < D := zero_lt_one.trans_le hD
  have hEPos : 0 < E := zero_lt_one.trans_le hE
  have hEPower : 0 <= E ^ largeSieveAlpha :=
    Real.rpow_nonneg hEPos.le _
  have hLPower : 0 <= L ^ hybridResidualGrowth :=
    Real.rpow_nonneg hL _
  have hdPower : d ^ largeSieveAlpha <= D ^ largeSieveAlpha :=
    Real.rpow_le_rpow hd hdD largeSieveAlpha_nonneg
  have hhead :
      E ^ largeSieveAlpha *
          (d ^ largeSieveAlpha * L ^ hybridResidualGrowth) <=
        (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth := by
    calc
      E ^ largeSieveAlpha *
          (d ^ largeSieveAlpha * L ^ hybridResidualGrowth) <=
        E ^ largeSieveAlpha *
          (D ^ largeSieveAlpha * L ^ hybridResidualGrowth) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdPower hLPower) hEPower
      _ = (D * E) ^ largeSieveAlpha *
          L ^ hybridResidualGrowth := by
        rw [Real.mul_rpow hDPos.le hEPos.le]
        ring
  have hratioPower :
      0 <= (Y / (D * E)) ^ (-hybridResidualHalfDecay) :=
    Real.rpow_nonneg (div_nonneg hY.le (mul_nonneg hDPos.le hEPos.le)) _
  have htailScale :
      E ^ largeSieveAlpha *
          (d * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) <=
        E ^ largeSieveAlpha *
          (D * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) := by
    apply mul_le_mul_of_nonneg_left _ hEPower
    apply mul_le_mul_of_nonneg_right _ hratioPower
    exact mul_le_mul_of_nonneg_right hdD hL
  have hEExponent :
      E ^ (largeSieveAlpha + hybridResidualHalfDecay) <=
        E ^ (5 / 6 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hE <| by
      norm_num [largeSieveAlpha, hybridResidualHalfDecay]
  have hDExponent :
      D ^ (1 + hybridResidualHalfDecay) <= D ^ (3 / 2 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hD <| by
      norm_num [hybridResidualHalfDecay]
  have htailNumerator :
      E ^ (largeSieveAlpha + hybridResidualHalfDecay) *
          D ^ (1 + hybridResidualHalfDecay) * L <=
        E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul hEExponent hDExponent
      (Real.rpow_nonneg hDPos.le _)
      (Real.rpow_nonneg hEPos.le _)
  have htail :
      E ^ largeSieveAlpha *
          (d * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) <=
        E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          Y ^ hybridResidualHalfDecay := by
    calc
      E ^ largeSieveAlpha *
          (d * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) <=
        E ^ largeSieveAlpha *
          (D * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)) := htailScale
      _ = E ^ largeSieveAlpha * D * L *
          (Y / (D * E)) ^ (-hybridResidualHalfDecay) := by ring
      _ = E ^ (largeSieveAlpha + hybridResidualHalfDecay) *
          D ^ (1 + hybridResidualHalfDecay) * L /
            Y ^ hybridResidualHalfDecay :=
        hybridPublishedTail_eq hDPos hEPos hY
      _ <= E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          Y ^ hybridResidualHalfDecay :=
        div_le_div_of_nonneg_right htailNumerator
          (Real.rpow_nonneg hY.le _)
  rw [mul_add]
  exact add_le_add hhead htail

/-- The first Alternative Hybrid Bound with the sharper coefficient inherited
from the exact formal dependency chain. The case `Q2 = 0` is retained as an
empty source band. -/
theorem decimalHybridAlignedSourceBandSum_le_publishedPowers
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    (hq₁Upper : q₁ <= Q₁) :
    let C : Real := ((10 ^ loss : Nat) : Real)
    let D : Real := ((10 ^ dLength : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    let Y : Real := ((10 ^ length : Nat) : Real)
    let L : Real := ((Q₁ * Q₂ ^ 2 : Nat) : Real)
    decimalHybridAlignedSourceBandSum digit length q₁ d Q₂ (10 ^ eLength) <=
      (72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
          (1 + C) * (3 + C ^ largeSieveSigma)) *
        ((D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            Y ^ hybridResidualHalfDecay) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let C : Real := ((10 ^ loss : Nat) : Real)
  let D : Real := ((10 ^ dLength : Nat) : Real)
  let E : Real := ((10 ^ eLength : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  let L : Real := ((Q₁ * Q₂ ^ 2 : Nat) : Real)
  let R : Real :=
    (d : Real) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
      (d : Real) * L * (Y / (D * E)) ^ (-hybridResidualHalfDecay)
  let U : Real :=
    20 * largeSieveSamplingConstant * (1 + 2 * C) * E ^ largeSieveAlpha
  let V : Real :=
    3600 * (1 + 2 * C) *
      (largeSieveSamplingConstant * (1 + C) *
        (3 + C ^ largeSieveSigma) * R)
  let H : Real :=
    72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
      (1 + C) * (3 + C ^ largeSieveSigma)
  let P : Real :=
    (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
      E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
        Y ^ hybridResidualHalfDecay
  change decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
      (10 ^ eLength) <= H * P
  by_cases hQ₂ : Q₂ = 0
  · subst Q₂
    simp [decimalHybridAlignedSourceBandSum, hybridResidualSourceDenominators,
      L, P, hybridResidualGrowth]
  · have hQ₂Pos : 0 < Q₂ := Nat.pos_of_ne_zero hQ₂
    have hfactor :=
      decimalHybridAlignedSourceBandSum_le_source_power_mul_squaredBlockSourceBandSum
        loss digit (length := length) (dLength := dLength)
        (eLength := eLength) (q₁ := q₁) (d := d) (u := u) (Q₂ := Q₂)
        hscale hq₁ hd hdvd hq₁10
    change decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
        (10 ^ eLength) <=
      (20 * largeSieveSamplingConstant * (2 * C + 1) *
          E ^ largeSieveAlpha) *
        decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
          (E / Y) at hfactor
    have hfactorU :
        decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
            (10 ^ eLength) <=
          U * decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
            (E / Y) := by
      calc
        decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
            (10 ^ eLength) <=
          (20 * largeSieveSamplingConstant * (2 * C + 1) *
              E ^ largeSieveAlpha) *
            decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
              (E / Y) := hfactor
        _ = U * decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
            (E / Y) := by
          dsimp [U]
          ring
    have hsquared :=
      decimalHybridSquaredBlockSourceBandSum_le_common_source_branch
        loss digit (length := length) (dLength := dLength)
        (eLength := eLength) (q₁ := q₁) (d := d) (u := u)
        (Q₁ := Q₁) (Q₂ := Q₂) hscale hq₁ hd hdD hdvd hq₁10
        hQ₂Pos hq₁Upper
    change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (E / Y) <= V at hsquared
    have hA : 0 <= largeSieveSamplingConstant := by
      norm_num [largeSieveSamplingConstant]
    have hC : 0 <= C := by dsimp [C]; positivity
    have hEPos : 0 < E := by dsimp [E]; positivity
    have hU : 0 <= U := by
      dsimp [U]
      positivity
    have hcomposed :
        decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
            (10 ^ eLength) <= U * V :=
      hfactorU.trans (mul_le_mul_of_nonneg_left hsquared hU)
    have hDOne : 1 <= D := by
      dsimp [D]
      have hDOneNat : 1 <= (10 : Nat) ^ dLength := one_le_pow₀ (by norm_num)
      exact_mod_cast hDOneNat
    have hEOne : 1 <= E := by
      dsimp [E]
      have hEOneNat : 1 <= (10 : Nat) ^ eLength := one_le_pow₀ (by norm_num)
      exact_mod_cast hEOneNat
    have hYPos : 0 < Y := by dsimp [Y]; positivity
    have hdDReal : (d : Real) <= D := by
      dsimp [D]
      exact_mod_cast hdD
    have hscalar := hybridCommonSourceBranch_le_publishedPowers
      (d := (d : Real)) (D := D) (E := E) (L := L) (Y := Y)
      (by positivity) hdDReal hDOne hEOne (by positivity) hYPos
    change E ^ largeSieveAlpha * R <= P at hscalar
    have hH : 0 <= H := by
      dsimp [H]
      positivity
    calc
      decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
          (10 ^ eLength) <= U * V := hcomposed
      _ = H * (E ^ largeSieveAlpha * R) := by
        dsimp [U, V, H]
        ring
      _ <= H * P := mul_le_mul_of_nonneg_left hscalar hH

/-- A coarser loss-only coefficient in which `C^(50/77)` is replaced by
`C`. -/
theorem decimalHybridAlignedSourceBandSum_le_publishedPowers_coarse
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    (hq₁Upper : q₁ <= Q₁) :
    let C : Real := ((10 ^ loss : Nat) : Real)
    let D : Real := ((10 ^ dLength : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    let Y : Real := ((10 ^ length : Nat) : Real)
    let L : Real := ((Q₁ * Q₂ ^ 2 : Nat) : Real)
    decimalHybridAlignedSourceBandSum digit length q₁ d Q₂ (10 ^ eLength) <=
      (72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
          (1 + C) * (3 + C)) *
        ((D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            Y ^ hybridResidualHalfDecay) := by
  let C : Real := ((10 ^ loss : Nat) : Real)
  let D : Real := ((10 ^ dLength : Nat) : Real)
  let E : Real := ((10 ^ eLength : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  let L : Real := ((Q₁ * Q₂ ^ 2 : Nat) : Real)
  let Hsharp : Real :=
    72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
      (1 + C) * (3 + C ^ largeSieveSigma)
  let Hcoarse : Real :=
    72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
      (1 + C) * (3 + C)
  let P : Real :=
    (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
      E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
        Y ^ hybridResidualHalfDecay
  change decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
      (10 ^ eLength) <= Hcoarse * P
  have hsharp := decimalHybridAlignedSourceBandSum_le_publishedPowers
    loss digit (length := length) (dLength := dLength)
      (eLength := eLength) (q₁ := q₁) (d := d) (u := u)
      (Q₁ := Q₁) (Q₂ := Q₂) hscale hq₁ hd hdD hdvd hq₁10 hq₁Upper
  change decimalHybridAlignedSourceBandSum digit length q₁ d Q₂
      (10 ^ eLength) <= Hsharp * P at hsharp
  have hCOneNat : 1 <= (10 : Nat) ^ loss := one_le_pow₀ (by norm_num)
  have hCOne : (1 : Real) <= C := by
    dsimp [C]
    exact_mod_cast hCOneNat
  have hCpower : C ^ largeSieveSigma <= C := by
    calc
      C ^ largeSieveSigma <= C ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hCOne
          (by norm_num [largeSieveSigma])
      _ = C := Real.rpow_one C
  have hA : 0 <= largeSieveSamplingConstant := by
    norm_num [largeSieveSamplingConstant]
  have hcoefficient : Hsharp <= Hcoarse := by
    dsimp [Hsharp, Hcoarse]
    apply mul_le_mul_of_nonneg_left
    · linarith
    · positivity
  have hP : 0 <= P := by
    dsimp [P]
    positivity
  exact hsharp.trans (mul_le_mul_of_nonneg_right hcoefficient hP)

end

end PrimesRestrictedDigits
