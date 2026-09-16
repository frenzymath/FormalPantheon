import PrimesRestrictedDigits.Fourier.Moment235CachedCosine

/-!
# Rational consequence of the exact cosine cache

Centered signed residuals are mapped to the checked half-period cache through
their natural absolute values. The endpoint `-50000` remains signed in the
cached numerator.
-/

namespace PrimesRestrictedDigits

def moment235CosineResidualIndex
    (residual : Int) (hlow : -50000 <= residual)
    (hhigh : residual <= 50000) : Fin 50001 :=
  ⟨residual.natAbs, by
    by_cases hresidual : 0 <= residual
    · rw [← Int.ofNat_lt, Int.natAbs_of_nonneg hresidual]
      omega
    · have hresidual' : residual <= 0 := by omega
      rw [← Int.ofNat_lt, Int.ofNat_natAbs_of_nonpos hresidual']
      omega⟩

theorem rationalCosineUpper20D20FixedNumerator_natAbs (x : Int) :
    rationalCosineUpper20D20FixedNumerator (x.natAbs : Int) =
      rationalCosineUpper20D20FixedNumerator x := by
  by_cases hx : 0 <= x
  · rw [Int.natAbs_of_nonneg hx]
  · have hx' : x <= 0 := by omega
    rw [Int.ofNat_natAbs_of_nonpos hx']
    exact rationalCosineUpper20D20FixedNumerator_neg x

theorem centeredResidual100000_natAbs_neg (x : Int) :
    (centeredResidual100000 (-x)).natAbs =
      (centeredResidual100000 x).natAbs := by
  unfold centeredResidual100000
  rw [Int.natAbs_eq_natAbs_iff]
  have hx := Int.emod_add_ediv_mul (x + 50000) 100000
  have hneg := Int.emod_add_ediv_mul (-x + 50000) 100000
  have hx0 := Int.emod_nonneg
    (x + 50000) (by norm_num : (100000 : Int) ≠ 0)
  have hx1 := Int.emod_lt_of_pos
    (x + 50000) (by norm_num : (0 : Int) < 100000)
  have hn0 := Int.emod_nonneg
    (-x + 50000) (by norm_num : (100000 : Int) ≠ 0)
  have hn1 := Int.emod_lt_of_pos
    (-x + 50000) (by norm_num : (0 : Int) < 100000)
  omega

theorem centeredResidual100000_natAbs_sub_period (multiple x : Int) :
    (centeredResidual100000 (100000 * multiple - x)).natAbs =
      (centeredResidual100000 x).natAbs := by
  have hresidual :
      centeredResidual100000 (100000 * multiple - x) =
        centeredResidual100000 (-x) := by
    unfold centeredResidual100000
    rw [show 100000 * multiple - x + 50000 =
        (-x + 50000) + 100000 * multiple by ring,
      Int.add_mul_emod_self_left]
  rw [hresidual, centeredResidual100000_natAbs_neg]

def moment235CenteredCosineUpperNumerator (x : Int) : Int :=
  let residual := centeredResidual100000 x
  let bounds := centeredResidual100000_bounds x
  moment235CosineUpperNumerator
    (moment235CosineResidualIndex residual bounds.1 (le_of_lt bounds.2))

theorem moment235CenteredCosineUpperNumerator_neg (x : Int) :
    moment235CenteredCosineUpperNumerator (-x) =
      moment235CenteredCosineUpperNumerator x := by
  unfold moment235CenteredCosineUpperNumerator
  apply congrArg moment235CosineUpperNumerator
  apply Fin.ext
  exact centeredResidual100000_natAbs_neg x

theorem moment235CenteredCosineUpperNumerator_sub_period
    (multiple x : Int) :
    moment235CenteredCosineUpperNumerator (100000 * multiple - x) =
      moment235CenteredCosineUpperNumerator x := by
  unfold moment235CenteredCosineUpperNumerator
  apply congrArg moment235CosineUpperNumerator
  apply Fin.ext
  exact centeredResidual100000_natAbs_sub_period multiple x

theorem rationalCosineUpper20D20Rat_le_moment235Cache
    (residual : Int) (hlow : -50000 <= residual)
    (hhigh : residual <= 50000) :
    rationalCosineUpper20D20Rat ((residual : Rat) / 100000) <=
      (moment235CosineUpperNumerator
          (moment235CosineResidualIndex residual hlow hhigh) : Rat) /
        moment235CosineScale := by
  rw [rationalCosineUpper20D20Rat_eq_fixedNumerator]
  have hcertificate := moment235CosineUpperNumerator_certificate
    (moment235CosineResidualIndex residual hlow hhigh)
  have hcross :
      (moment235CosineScale : Int) *
          rationalCosineUpper20D20FixedNumerator residual <=
        (rationalCosineUpper20D20FixedDenominator : Int) *
          moment235CosineUpperNumerator
            (moment235CosineResidualIndex residual hlow hhigh) := by
    simpa only [moment235CosineResidualIndex,
      rationalCosineUpper20D20FixedNumerator_natAbs] using hcertificate
  have hcrossRat :
      (moment235CosineScale : Rat) *
          rationalCosineUpper20D20FixedNumerator residual <=
        (rationalCosineUpper20D20FixedDenominator : Rat) *
          moment235CosineUpperNumerator
            (moment235CosineResidualIndex residual hlow hhigh) := by
    exact_mod_cast hcross
  have hdenominator :
      (0 : Rat) < rationalCosineUpper20D20FixedDenominator := by
    rw [rationalCosineUpper20D20FixedDenominator_eq]
    norm_num [rationalCosineUpper20D20BaseDenominator]
  have hscale : (0 : Rat) < moment235CosineScale := by
    norm_num [moment235CosineScale]
  apply (div_le_div_iff₀ hdenominator hscale).2
  simpa [mul_comm] using hcrossRat

theorem rationalCosineUpper20D20Rat_centered_le_moment235Cache (x : Int) :
    rationalCosineUpper20D20Rat
        ((centeredResidual100000 x : Rat) / 100000) <=
      (moment235CenteredCosineUpperNumerator x : Rat) /
        moment235CosineScale := by
  have hbounds := centeredResidual100000_bounds x
  simpa only [moment235CenteredCosineUpperNumerator] using
    rationalCosineUpper20D20Rat_le_moment235Cache
      (centeredResidual100000 x) hbounds.1 (le_of_lt hbounds.2)

end PrimesRestrictedDigits
