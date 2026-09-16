import PrimesRestrictedDigits.Fourier.HybridSquaredBlockSourceSum

/-!
# Denominator-Power Balance for the Hybrid Source Bound

This file collapses the two canonical denominator-weighted branches in published Lemma 10.7 to
one common source term. See `MAYNARD-PRD-PUBLISHED`, pp. 183--185.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem factorPowerBranch_le
    {x y d L T alpha beta : Real}
    (hx : 1 <= x) (hy : 1 <= y) (hL : 0 <= L) (hT : 0 <= T)
    (hfactor : x * y = d) (hbetaAlpha : beta <= alpha)
    (hAlphaOne : alpha <= 1) :
    y ^ alpha * ((x * L) ^ beta + (x * L) * T) <=
      d ^ alpha * L ^ beta + d * L * T := by
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hy0 : 0 <= y := zero_le_one.trans hy
  have hxPower : x ^ beta <= x ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hx hbetaAlpha
  have hyPower : y ^ alpha <= y := by
    calc
      y ^ alpha <= y ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hy hAlphaOne
      _ = y := Real.rpow_one y
  have hhead :
      y ^ alpha * (x * L) ^ beta <= d ^ alpha * L ^ beta := by
    calc
      y ^ alpha * (x * L) ^ beta =
          y ^ alpha * (x ^ beta * L ^ beta) := by
        rw [Real.mul_rpow hx0 hL]
      _ <= y ^ alpha * (x ^ alpha * L ^ beta) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hxPower (Real.rpow_nonneg hL _))
          (Real.rpow_nonneg hy0 _)
      _ = (x * y) ^ alpha * L ^ beta := by
        rw [Real.mul_rpow hx0 hy0]
        ring
      _ = d ^ alpha * L ^ beta := by rw [hfactor]
  have hrest : 0 <= (x * L) * T :=
    mul_nonneg (mul_nonneg hx0 hL) hT
  have htail :
      y ^ alpha * ((x * L) * T) <= d * L * T := by
    calc
      y ^ alpha * ((x * L) * T) <= y * ((x * L) * T) :=
        mul_le_mul_of_nonneg_right hyPower hrest
      _ = d * L * T := by rw [← hfactor]; ring
  calc
    y ^ alpha * ((x * L) ^ beta + (x * L) * T) =
        y ^ alpha * (x * L) ^ beta +
          y ^ alpha * ((x * L) * T) := by ring
    _ <= d ^ alpha * L ^ beta + d * L * T :=
      add_le_add hhead htail

/-- The first canonical denominator grouping contributes at most the common
source branch. -/
theorem hybridFirstDenominatorPowerBranch_le
    {d k v L : Nat} {Z : Real} (hd : 0 < d) (hZ : 0 < Z) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (d₃ : Real) ^ largeSieveAlpha *
        (((((d₁ * d₂) * L : Nat) : Real) ^ hybridResidualGrowth) +
          (((d₁ * d₂) * L : Nat) : Real) *
            Z ^ (-hybridResidualHalfDecay)) <=
      (d : Real) ^ largeSieveAlpha *
          (L : Real) ^ hybridResidualGrowth +
        (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay) := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  change (d₃ : Real) ^ largeSieveAlpha *
      (((((d₁ * d₂) * L : Nat) : Real) ^ hybridResidualGrowth) +
        (((d₁ * d₂) * L : Nat) : Real) *
          Z ^ (-hybridResidualHalfDecay)) <=
    (d : Real) ^ largeSieveAlpha *
        (L : Real) ^ hybridResidualGrowth +
      (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay)
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hxNat : 1 <= d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  have hyNat : 1 <= d₃ := hd₃
  have hx : (1 : Real) <= (d₁ * d₂ : Nat) := by exact_mod_cast hxNat
  have hy : (1 : Real) <= d₃ := by exact_mod_cast hyNat
  have hfactorNat : d₁ * d₂ * d₃ = d := by
    exact hybridDenominatorFirstSecondThird_eq d (10 ^ k) (10 ^ v)
  have hfactor : ((d₁ * d₂ : Nat) : Real) * (d₃ : Real) = (d : Real) := by
    exact_mod_cast hfactorNat
  have hbound := factorPowerBranch_le
    (x := ((d₁ * d₂ : Nat) : Real)) (y := (d₃ : Real))
    (d := (d : Real)) (L := (L : Real))
    (T := Z ^ (-hybridResidualHalfDecay))
    (alpha := largeSieveAlpha) (beta := hybridResidualGrowth)
    hx hy (by positivity) (Real.rpow_nonneg hZ.le _) hfactor
    (by norm_num [hybridResidualGrowth, largeSieveAlpha])
    (by norm_num [largeSieveAlpha])
  simpa only [Nat.cast_mul] using hbound

/-- The second canonical denominator grouping contributes at most the same
common source branch. -/
theorem hybridSecondDenominatorPowerBranch_le
    {d k v L : Nat} {Z : Real} (hd : 0 < d) (hZ : 0 < Z) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha *
        ((((d₁ * L : Nat) : Real) ^ hybridResidualGrowth) +
          ((d₁ * L : Nat) : Real) * Z ^ (-hybridResidualHalfDecay)) <=
      (d : Real) ^ largeSieveAlpha *
          (L : Real) ^ hybridResidualGrowth +
        (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay) := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  change ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha *
      ((((d₁ * L : Nat) : Real) ^ hybridResidualGrowth) +
        ((d₁ * L : Nat) : Real) * Z ^ (-hybridResidualHalfDecay)) <=
    (d : Real) ^ largeSieveAlpha *
        (L : Real) ^ hybridResidualGrowth +
      (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay)
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hxNat : 1 <= d₁ := hd₁
  have hyNat : 1 <= d₂ * d₃ := Nat.mul_pos hd₂ hd₃
  have hx : (1 : Real) <= d₁ := by exact_mod_cast hxNat
  have hy : (1 : Real) <= (d₂ * d₃ : Nat) := by exact_mod_cast hyNat
  have hfactorNat : d₁ * (d₂ * d₃) = d := by
    simpa only [mul_assoc] using
      (hybridDenominatorFirstSecondThird_eq d (10 ^ k) (10 ^ v))
  have hfactor : (d₁ : Real) * ((d₂ * d₃ : Nat) : Real) = (d : Real) := by
    exact_mod_cast hfactorNat
  have hbound := factorPowerBranch_le
    (x := (d₁ : Real)) (y := ((d₂ * d₃ : Nat) : Real))
    (d := (d : Real)) (L := (L : Real))
    (T := Z ^ (-hybridResidualHalfDecay))
    (alpha := largeSieveAlpha) (beta := hybridResidualGrowth)
    hx hy (by positivity) (Real.rpow_nonneg hZ.le _) hfactor
    (by norm_num [hybridResidualGrowth, largeSieveAlpha])
    (by norm_num [largeSieveAlpha])
  simpa only [Nat.cast_mul] using hbound

private theorem weightedDenominatorBranches_le_common
    {A C first second common : Real} (hA : 0 <= A) (hC : 0 <= C)
    (hfirst : first <= common) (hsecond : second <= common) :
    (2 * A * (1 + C)) * first +
        (A * (1 + C) * (1 + C ^ largeSieveSigma)) * second <=
      A * (1 + C) * (3 + C ^ largeSieveSigma) * common := by
  have hfirstCoefficient : 0 <= 2 * A * (1 + C) := by positivity
  have hsecondCoefficient :
      0 <= A * (1 + C) * (1 + C ^ largeSieveSigma) := by
    positivity
  calc
    (2 * A * (1 + C)) * first +
          (A * (1 + C) * (1 + C ^ largeSieveSigma)) * second <=
        (2 * A * (1 + C)) * common +
          (A * (1 + C) * (1 + C ^ largeSieveSigma)) * common :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfirst hfirstCoefficient)
        (mul_le_mul_of_nonneg_left hsecond hsecondCoefficient)
    _ = A * (1 + C) * (3 + C ^ largeSieveSigma) * common := by ring

/-- After the outer residual composition, both canonical denominator powers
collapse to one common source branch. -/
theorem decimalHybridSquaredBlockSourceBandSum_le_common_source_branch
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    (hQ₂ : 0 < Q₂) (hq₁Upper : q₁ <= Q₁) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let C : Real := ((10 ^ loss : Nat) : Real)
    let B : Real := 3600 * (1 + 2 * C)
    let L : Nat := Q₁ * Q₂ ^ 2
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) <=
      B *
        (largeSieveSamplingConstant * (1 + C) *
          (3 + C ^ largeSieveSigma) *
            ((d : Real) ^ largeSieveAlpha *
                (L : Real) ^ hybridResidualGrowth +
              (d : Real) * (L : Real) *
                Z ^ (-hybridResidualHalfDecay))) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ dAux) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ dAux)
  let C : Real := ((10 ^ loss : Nat) : Real)
  let B : Real := 3600 * (1 + 2 * C)
  let L : Nat := Q₁ * Q₂ ^ 2
  let P₁ : Real := (((d₁ * d₂) * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let P₂ : Real := ((d₁ * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  let R : Real :=
    (d : Real) ^ largeSieveAlpha *
        (L : Real) ^ hybridResidualGrowth +
      (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay)
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (((10 ^ eLength : Nat) : Real) /
        ((10 ^ length : Nat) : Real)) <=
    B * (largeSieveSamplingConstant * (1 + C) *
      (3 + C ^ largeSieveSigma) * R)
  have hsource := decimalHybridSquaredBlockSourceBandSum_le_source_branches
    loss digit (length := length) (dLength := dLength)
      (eLength := eLength) (q₁ := q₁) (d := d) (u := u)
      (Q₁ := Q₁) (Q₂ := Q₂) hscale hq₁ hd hdD hdvd hq₁10 hQ₂ hq₁Upper
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (((10 ^ eLength : Nat) : Real) /
        ((10 ^ length : Nat) : Real)) <=
    B *
      ((2 * largeSieveSamplingConstant * (1 + C) *
          (d₃ : Real) ^ largeSieveAlpha) *
            (P₁ ^ hybridResidualGrowth +
              P₁ * Z ^ (-hybridResidualHalfDecay)) +
        (largeSieveSamplingConstant * (1 + C) *
          (1 + C ^ largeSieveSigma) *
            ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
              (P₂ ^ hybridResidualGrowth +
                P₂ * Z ^ (-hybridResidualHalfDecay))) at hsource
  have hZ : 0 < Z := by
    dsimp [Z]
    positivity
  have hfirst := hybridFirstDenominatorPowerBranch_le
    (d := d) (k := dAux) (v := v) (L := L) (Z := Z) hd hZ
  dsimp only at hfirst
  have hfirst' : (d₃ : Real) ^ largeSieveAlpha *
      (P₁ ^ hybridResidualGrowth +
        P₁ * Z ^ (-hybridResidualHalfDecay)) <= R := by
    simpa only [P₁, L, R, Nat.cast_mul, mul_assoc] using hfirst
  have hsecond := hybridSecondDenominatorPowerBranch_le
    (d := d) (k := dAux) (v := v) (L := L) (Z := Z) hd hZ
  dsimp only at hsecond
  have hsecond' : ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha *
      (P₂ ^ hybridResidualGrowth +
        P₂ * Z ^ (-hybridResidualHalfDecay)) <= R := by
    simpa only [P₂, L, R, Nat.cast_mul, mul_assoc] using hsecond
  have hA : 0 <= largeSieveSamplingConstant := by
    norm_num [largeSieveSamplingConstant]
  have hC : 0 <= C := by dsimp [C]; positivity
  have hcombine := weightedDenominatorBranches_le_common
    hA hC hfirst' hsecond'
  have hB : 0 <= B := by dsimp [B, C]; positivity
  calc
    decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) <=
      B *
        ((2 * largeSieveSamplingConstant * (1 + C) *
            (d₃ : Real) ^ largeSieveAlpha) *
              (P₁ ^ hybridResidualGrowth +
                P₁ * Z ^ (-hybridResidualHalfDecay)) +
          (largeSieveSamplingConstant * (1 + C) *
            (1 + C ^ largeSieveSigma) *
              ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
                (P₂ ^ hybridResidualGrowth +
                  P₂ * Z ^ (-hybridResidualHalfDecay))) := hsource
    _ = B *
        ((2 * largeSieveSamplingConstant * (1 + C)) *
            ((d₃ : Real) ^ largeSieveAlpha *
              (P₁ ^ hybridResidualGrowth +
                P₁ * Z ^ (-hybridResidualHalfDecay))) +
          (largeSieveSamplingConstant * (1 + C) *
            (1 + C ^ largeSieveSigma)) *
              (((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha *
                (P₂ ^ hybridResidualGrowth +
                  P₂ * Z ^ (-hybridResidualHalfDecay)))) := by ring
    _ <= B * (largeSieveSamplingConstant * (1 + C) *
        (3 + C ^ largeSieveSigma) * R) :=
      mul_le_mul_of_nonneg_left hcombine hB

/-- At the decimal loss scale, the remaining `C^(50/77)` coefficient is at
most the linear loss `C`. -/
theorem decimalHybridSquaredBlockSourceBandSum_le_common_source_branch_coarse
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    (hQ₂ : 0 < Q₂) (hq₁Upper : q₁ <= Q₁) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let C : Real := ((10 ^ loss : Nat) : Real)
    let B : Real := 3600 * (1 + 2 * C)
    let L : Nat := Q₁ * Q₂ ^ 2
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) <=
      B *
        (largeSieveSamplingConstant * (1 + C) * (3 + C) *
          ((d : Real) ^ largeSieveAlpha *
              (L : Real) ^ hybridResidualGrowth +
            (d : Real) * (L : Real) *
              Z ^ (-hybridResidualHalfDecay))) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let C : Real := ((10 ^ loss : Nat) : Real)
  let B : Real := 3600 * (1 + 2 * C)
  let L : Nat := Q₁ * Q₂ ^ 2
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  let R : Real :=
    (d : Real) ^ largeSieveAlpha *
        (L : Real) ^ hybridResidualGrowth +
      (d : Real) * (L : Real) * Z ^ (-hybridResidualHalfDecay)
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (((10 ^ eLength : Nat) : Real) /
        ((10 ^ length : Nat) : Real)) <=
    B * (largeSieveSamplingConstant * (1 + C) * (3 + C) * R)
  have hsharp :=
    decimalHybridSquaredBlockSourceBandSum_le_common_source_branch
      loss digit (length := length) (dLength := dLength)
        (eLength := eLength) (q₁ := q₁) (d := d) (u := u)
        (Q₁ := Q₁) (Q₂ := Q₂) hscale hq₁ hd hdD hdvd hq₁10 hQ₂ hq₁Upper
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (((10 ^ eLength : Nat) : Real) /
        ((10 ^ length : Nat) : Real)) <=
    B * (largeSieveSamplingConstant * (1 + C) *
      (3 + C ^ largeSieveSigma) * R) at hsharp
  have hCOneNat : 1 <= (10 : Nat) ^ loss :=
    one_le_pow₀ (by norm_num)
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
  have hC : 0 <= C := hCOne.trans' (by norm_num)
  have hcoefficient :
      largeSieveSamplingConstant * (1 + C) *
          (3 + C ^ largeSieveSigma) <=
        largeSieveSamplingConstant * (1 + C) * (3 + C) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact mul_nonneg hA (by linarith)
  have hR : 0 <= R := by
    dsimp [R]
    positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  exact hsharp.trans <| mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcoefficient hR) hB

end

end PrimesRestrictedDigits
