import PrimesRestrictedDigits.Fourier.HybridAuxiliaryBlocks
import PrimesRestrictedDigits.Fourier.HybridResidualDecay
import PrimesRestrictedDigits.Fourier.HybridResidualPrefix
import PrimesRestrictedDigits.Fourier.LargeSieveScaleSelection
import PrimesRestrictedDigits.Fourier.SquaredTransformTwoScaleSampling

/-!
# Residual Source-Bound Assembly

This file gives an explicit replacement for equation (10.16) in Maynard's Lemma 10.7. See
`MAYNARD-PRD-PUBLISHED`, pp. 184--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The source ratio using the original decimal blocks is no larger than the
weak square-scale endpoint selected from the auxiliary blocks. -/
theorem decimalHybridAuxiliary_originalSquareRatio_le
    (length dLength eLength : Nat) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real)) <=
      10 * ((10 ^ v : Nat) : Real) ^ 2 := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  change ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real)) <=
    10 * ((10 ^ v : Nat) : Real) ^ 2
  have hdAux : dAux <= dLength := by
    dsimp [dAux, decimalHybridAuxiliaryDLength]
    omega
  have heAux : eAux <= eLength := by
    dsimp [eAux, decimalHybridAuxiliaryELength]
    omega
  have hblocks : dAux + eAux <= length := by
    dsimp [dAux, eAux, decimalHybridAuxiliaryDLength,
      decimalHybridAuxiliaryELength]
    omega
  have hdPow : 10 ^ dAux <= 10 ^ dLength :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).2 hdAux
  have hePow : 10 ^ eAux <= 10 ^ eLength :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).2 heAux
  have hdenNat :
      10 ^ dAux * 10 ^ eAux <= 10 ^ dLength * 10 ^ eLength :=
    Nat.mul_le_mul hdPow hePow
  have hden :
      ((10 ^ dAux : Nat) : Real) * ((10 ^ eAux : Nat) : Real) <=
        ((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real) := by
    exact_mod_cast hdenNat
  have hratio :
      ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real)) <=
        ((10 ^ length : Nat) : Real) /
          (((10 ^ dAux : Nat) : Real) *
            ((10 ^ eAux : Nat) : Real)) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have haux := decimalHybridSquareScale_real_square_ratio hblocks
  change ((10 ^ v : Nat) : Real) ^ 2 <=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dAux : Nat) : Real) *
          ((10 ^ eAux : Nat) : Real)) ∧
    ((10 ^ length : Nat) : Real) /
        (((10 ^ dAux : Nat) : Real) *
          ((10 ^ eAux : Nat) : Real)) <=
      10 * ((10 ^ v : Nat) : Real) ^ 2 at haux
  exact hratio.trans haux.2

/-- Sharp explicit residual source bound. The only prefix loss is ordinary
decimal rounding at the paper scale `P = m * Q1 * Q2^2`. -/
theorem hybridResidualReducedSourceSum_le_source_branches
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength m q Q1 Q2 : Nat} {delta : Real}
    (hscale : dLength + eLength <= length + loss)
    (hm : 0 < m) (hq : 0 < q) (hQ2 : 0 < Q2)
    (hqUpper : q <= Q1) (hdelta : 0 <= delta)
    (hdeltaUpper :
      delta <=
        (((10 ^ decimalHybridAuxiliaryDLength length dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real) *
            ((10 ^ decimalHybridSquareScaleLength length
              (decimalHybridAuxiliaryDLength length dLength)
              (decimalHybridAuxiliaryELength length dLength eLength) : Nat) : Real)) /
          ((10 ^ length : Nat) : Real)) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let P : Real := ((m * Q1 * Q2 ^ 2 : Nat) : Real)
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
      36 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
        10 ^ hybridResidualDecay *
        (P ^ hybridResidualGrowth +
          10 ^ hybridResidualHalfDecay *
            P * Z ^ (-hybridResidualHalfDecay)) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let P : Real := ((m * Q1 * Q2 ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  let K : Real := ((10 ^ loss : Nat) : Real)
  change hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
    36 * (1 + 2 * K) * 10 ^ hybridResidualDecay *
      (P ^ hybridResidualGrowth +
        10 ^ hybridResidualHalfDecay *
          P * Z ^ (-hybridResidualHalfDecay))
  have hQ1 : 0 < Q1 := hq.trans_le hqUpper
  have hPnat : 0 < m * Q1 * Q2 ^ 2 :=
    Nat.mul_pos (Nat.mul_pos hm hQ1) (pow_pos hQ2 2)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hPone : 1 <= P := by
    dsimp [P]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hPnat.ne'
  obtain ⟨r, hrv, hrP, hrV, hclose, _⟩ :=
    exists_largeSieve_decimalPrefix hPone v
  have hR : (0 : Real) <= ((10 ^ r : Nat) : Real) := by positivity
  have hprefix :
      min (((10 ^ v : Nat) : Real)) P <=
        10 * ((10 ^ r : Nat) : Real) := by
    exact le_of_lt (by simpa [min_comm] using hclose)
  have hdensityBase := decimalHybridAuxiliary_residualWindowDensity
    (length := length) (dLength := dLength) (eLength := eLength)
    (loss := loss) (r := r) hscale hrv
  change
    ((((10 ^ dAux : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
          ((10 ^ v : Nat) : Real)) /
        ((10 ^ length : Nat) : Real)) *
        ((10 ^ r : Nat) : Real) <= K at hdensityBase
  have hdensity :
      delta * ((10 ^ r : Nat) : Real) <= K := by
    exact (mul_le_mul_of_nonneg_right hdeltaUpper hR).trans hdensityBase
  have hM : 0 < m * q := Nat.mul_pos hm hq
  have hactualNat :
      (m * q) * Q2 ^ 2 <= m * Q1 * Q2 ^ 2 := by
    exact Nat.mul_le_mul_right (Q2 ^ 2)
      (Nat.mul_le_mul_left m hqUpper)
  have hactual :
      ((m * q : Nat) : Real) * (Q2 : Real) ^ 2 <= P := by
    dsimp [P]
    exact_mod_cast hactualNat
  have hactualPos :
      (0 : Real) < ((m * q : Nat) : Real) * (Q2 : Real) ^ 2 := by
    positivity
  have hseparated :
      ∀ left ∈ hybridResidualFractionSourceCarrier (m * q) Q2,
        ∀ right ∈ hybridResidualFractionSourceCarrier (m * q) Q2,
          left ≠ right ->
            1 / P <=
              dist ((hybridResidualFractionValue (m * q) left : Real) :
                  UnitAddCircle)
                ((hybridResidualFractionValue (m * q) right : Real) :
                  UnitAddCircle) := by
    intro left hleft right hright hne
    have hleftParent :
        left ∈ hybridResidualFractionCarrier (m * q) Q2 :=
      (Finset.mem_filter.mp hleft).1
    have hrightParent :
        right ∈ hybridResidualFractionCarrier (m * q) Q2 :=
      (Finset.mem_filter.mp hright).1
    have hspacing := one_div_mul_sq_le_dist_hybridResidualFractionValue
      hM hQ2 left hleftParent right hrightParent hne
    have hweaken :
        1 / P <=
          1 / (((m * q : Nat) : Real) * (Q2 : Real) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) hactualPos hactual
    exact hweaken.trans hspacing
  have hK : 0 <= K := by dsimp [K]; positivity
  have hsamplePair :=
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_of_decimalScale
      (hybridResidualFractionSourceCarrier (m * q) Q2) digit r
      (hybridResidualFractionValue (m * q)) hPone hdelta hK hrP hdensity
      hseparated 0
  have hsample :
      hybridResidualReducedSourceSum digit r (m * q) Q2 delta <=
        36 * (1 + 2 * K) * P / (9 : Real) ^ r := by
    rw [hybridResidualReducedSourceSum_eq_fractionSourceCarrier]
    simpa only [add_zero] using hsamplePair
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : (0 : Real) < ((10 ^ v : Nat) : Real) := by positivity
  have hZscale := decimalHybridAuxiliary_originalSquareRatio_le
    length dLength eLength
  change Z <= 10 * ((10 ^ v : Nat) : Real) ^ 2 at hZscale
  have hdecay := hybridResidual_denominator_le_source_branches
    hP hV hZ (by norm_num : (0 : Real) < 10) r hprefix hZscale
  have hcoefficient : 0 <= 36 * (1 + 2 * K) := by positivity
  calc
    hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
        hybridResidualReducedSourceSum digit r (m * q) Q2 delta :=
      hybridResidualReducedSourceSum_le_prefix digit hrv hdelta
    _ <= 36 * (1 + 2 * K) * P / (9 : Real) ^ r := hsample
    _ = (36 * (1 + 2 * K)) * (P / (9 : Real) ^ r) := by ring
    _ <= (36 * (1 + 2 * K)) *
        (10 ^ hybridResidualDecay *
          (P ^ hybridResidualGrowth +
            10 ^ hybridResidualHalfDecay *
              P * Z ^ (-hybridResidualHalfDecay))) :=
      mul_le_mul_of_nonneg_left hdecay hcoefficient
    _ = 36 * (1 + 2 * K) * 10 ^ hybridResidualDecay *
        (P ^ hybridResidualGrowth +
          10 ^ hybridResidualHalfDecay *
            P * Z ^ (-hybridResidualHalfDecay)) := by ring

/-- Coarse source-facing form of the residual bound with all decimal
real-power losses absorbed into the integer coefficient `3600`. -/
theorem hybridResidualReducedSourceSum_le_source_branches_coarse
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength m q Q1 Q2 : Nat} {delta : Real}
    (hscale : dLength + eLength <= length + loss)
    (hm : 0 < m) (hq : 0 < q) (hQ2 : 0 < Q2)
    (hqUpper : q <= Q1) (hdelta : 0 <= delta)
    (hdeltaUpper :
      delta <=
        (((10 ^ decimalHybridAuxiliaryDLength length dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real) *
            ((10 ^ decimalHybridSquareScaleLength length
              (decimalHybridAuxiliaryDLength length dLength)
              (decimalHybridAuxiliaryELength length dLength eLength) : Nat) : Real)) /
          ((10 ^ length : Nat) : Real)) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let P : Real := ((m * Q1 * Q2 ^ 2 : Nat) : Real)
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
      3600 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
        (P ^ hybridResidualGrowth +
          P * Z ^ (-hybridResidualHalfDecay)) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let P : Real := ((m * Q1 * Q2 ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  let K : Real := ((10 ^ loss : Nat) : Real)
  change hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
    3600 * (1 + 2 * K) *
      (P ^ hybridResidualGrowth +
        P * Z ^ (-hybridResidualHalfDecay))
  have hsharp := hybridResidualReducedSourceSum_le_source_branches
    loss digit hscale hm hq hQ2 hqUpper hdelta hdeltaUpper
  change hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
    36 * (1 + 2 * K) * 10 ^ hybridResidualDecay *
      (P ^ hybridResidualGrowth +
        10 ^ hybridResidualHalfDecay *
          P * Z ^ (-hybridResidualHalfDecay)) at hsharp
  have hdecayLe : hybridResidualDecay <= 1 := by
    norm_num [hybridResidualDecay]
  have hhalfLe : hybridResidualHalfDecay <= 1 := by
    norm_num [hybridResidualHalfDecay]
  have htenDecay : (10 : Real) ^ hybridResidualDecay <= 10 := by
    calc
      (10 : Real) ^ hybridResidualDecay <= (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdecayLe
      _ = 10 := Real.rpow_one 10
  have htenHalf : (10 : Real) ^ hybridResidualHalfDecay <= 10 := by
    calc
      (10 : Real) ^ hybridResidualHalfDecay <= (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalfLe
      _ = 10 := Real.rpow_one 10
  let first := P ^ hybridResidualGrowth
  let second := P * Z ^ (-hybridResidualHalfDecay)
  have hfirst : 0 <= first := by dsimp [first]; positivity
  have hsecond : 0 <= second := by dsimp [second]; positivity
  have hinside :
      (10 : Real) ^ hybridResidualDecay *
          (first + (10 : Real) ^ hybridResidualHalfDecay * second) <=
        100 * (first + second) := by
    calc
      (10 : Real) ^ hybridResidualDecay *
          (first + (10 : Real) ^ hybridResidualHalfDecay * second) <=
          10 * (first + (10 : Real) ^ hybridResidualHalfDecay * second) :=
        mul_le_mul_of_nonneg_right htenDecay
          (add_nonneg hfirst (mul_nonneg (by positivity) hsecond))
      _ <= 10 * (first + 10 * second) := by
        gcongr
      _ <= 100 * (first + second) := by nlinarith
  have hcoefficient : 0 <= 36 * (1 + 2 * K) := by
    dsimp [K]
    positivity
  calc
    hybridResidualReducedSourceSum digit v (m * q) Q2 delta <=
        36 * (1 + 2 * K) * (10 ^ hybridResidualDecay *
          (first + 10 ^ hybridResidualHalfDecay * second)) := by
      simpa [first, second, mul_assoc] using hsharp
    _ <= 36 * (1 + 2 * K) * (100 * (first + second)) :=
      mul_le_mul_of_nonneg_left hinside hcoefficient
    _ = 3600 * (1 + 2 * K) * (first + second) := by ring
    _ = _ := by rfl

end

end PrimesRestrictedDigits
