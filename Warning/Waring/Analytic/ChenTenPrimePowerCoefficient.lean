import Waring.Analytic.ChenTenSingularSeries

/-!
# Prime-power bounds for Chen's singular coefficients

Chen's local complete-sum estimate gives a quadratic bound for each
prime-power singular coefficient [CHEN1964-EN, pp. 1547-1548, 1565-1567;
CHEN1964-ZH, pp. 715-716, 731-733].
-/

namespace Waring.Analytic

/-- An arbitrary prime-power complete-sum constant passes to the fifteenth
power in Chen's singular coefficient. -/
theorem norm_chenTenSingularCoefficientNat_primePow_le_of_completePowerSum
    {p alpha : Nat} [NeZero p] (K : Real) (hK : 0 <= K) (n : Nat)
    (hcomplete : ∀ a : ZMod (p ^ alpha), IsUnit a ->
      ‖completePowerSum 5 a‖ <=
        K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) :
    ‖chenTenSingularCoefficientNat n (p ^ alpha)‖ <=
      K ^ 15 * (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  have hpow : p ^ alpha ≠ 0 := pow_ne_zero alpha (NeZero.ne p)
  have hq : (0 : Real) < (p ^ alpha : Nat) := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) alpha
  simp only [chenTenSingularCoefficientNat, dif_neg hpow]
  have hbound := norm_chenTenSingularCoefficient_le (p ^ alpha) n
    (K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)))
    (mul_nonneg hK (Real.rpow_nonneg hq.le _)) hcomplete
  have hdiv :
      (K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) /
          (p ^ alpha : Nat) =
        K * (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) *
          (((p ^ alpha : Nat) : Real) ^ (-1 : Real)) =
          K * ((((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) *
            (((p ^ alpha : Nat) : Real) ^ (-1 : Real))) := by ring
      _ = K * (((p ^ alpha : Nat) : Real) ^
          ((4 / 5 : Real) + (-1 : Real))) := by
        rw [← Real.rpow_add hq]
      _ = K * (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) := by
        norm_num
  have hpowFifteen :
      ((((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) ^ 15) =
        ((p ^ alpha : Nat) : Real) ^ (-3 : Real) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hq.le]
    congr 2
    norm_num
  have hcombine :
      ((p ^ alpha : Nat) : Real) *
          ((p ^ alpha : Nat) : Real) ^ (-3 : Real) =
        ((p ^ alpha : Nat) : Real) ^ (-2 : Real) := by
    conv_lhs => lhs; rw [← Real.rpow_one ((p ^ alpha : Nat) : Real)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    ‖chenTenSingularCoefficient (p ^ alpha) n‖ <=
        (p ^ alpha : Nat) *
          ((K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) /
            (p ^ alpha : Nat)) ^ 15 := hbound
    _ = ((p ^ alpha : Nat) : Real) *
        (K * (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real))) ^ 15 := by
      rw [hdiv]
    _ = K ^ 15 * (((p ^ alpha : Nat) : Real) *
        ((((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) ^ 15)) := by
      ring
    _ = K ^ 15 * (((p ^ alpha : Nat) : Real) *
        ((p ^ alpha : Nat) : Real) ^ (-3 : Real)) := by
      rw [hpowFifteen]
    _ = K ^ 15 *
        (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
      rw [hcombine]

/-- At a positive prime power, the singular coefficient inherits the
fifteenth power of Chen's local complete-sum factor. -/
theorem norm_chenTenSingularCoefficient_primePow_le_chenTwo
    {p alpha : Nat} [NeZero p] (hp : p.Prime) (hAlpha : 0 < alpha)
    (n : Nat) :
    ‖chenTenSingularCoefficient (p ^ alpha) n‖ <=
      chenTwoPrimeFactor p ^ 15 *
        (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  have hq : (0 : Real) < (p ^ alpha : Nat) := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) alpha
  have hFactor : 0 <= chenTwoPrimeFactor p :=
    chenTwoPrimeFactor_nonneg p
  have hbound := norm_chenTenSingularCoefficient_le (p ^ alpha) n
    (chenTwoPrimeFactor p *
      (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)))
    (mul_nonneg hFactor (Real.rpow_nonneg hq.le _))
    (fun a ha => chen_two_primePower hp hAlpha a ha)
  have hdiv :
      (chenTwoPrimeFactor p *
          (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) /
          (p ^ alpha : Nat) =
        chenTwoPrimeFactor p *
          (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      chenTwoPrimeFactor p *
            (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) *
          (((p ^ alpha : Nat) : Real) ^ (-1 : Real)) =
          chenTwoPrimeFactor p *
            ((((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) *
              (((p ^ alpha : Nat) : Real) ^ (-1 : Real))) := by ring
      _ = chenTwoPrimeFactor p *
          (((p ^ alpha : Nat) : Real) ^
            ((4 / 5 : Real) + (-1 : Real))) := by
        rw [← Real.rpow_add hq]
      _ = chenTwoPrimeFactor p *
          (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) := by
        norm_num
  have hpow :
      ((((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) ^ 15) =
        ((p ^ alpha : Nat) : Real) ^ (-3 : Real) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hq.le]
    congr 2
    norm_num
  have hcombine :
      ((p ^ alpha : Nat) : Real) *
          ((p ^ alpha : Nat) : Real) ^ (-3 : Real) =
        ((p ^ alpha : Nat) : Real) ^ (-2 : Real) := by
    conv_lhs => lhs; rw [← Real.rpow_one ((p ^ alpha : Nat) : Real)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    ‖chenTenSingularCoefficient (p ^ alpha) n‖ <=
        (p ^ alpha : Nat) *
          ((chenTwoPrimeFactor p *
            (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) /
            (p ^ alpha : Nat)) ^ 15 := hbound
    _ = ((p ^ alpha : Nat) : Real) *
        (chenTwoPrimeFactor p *
          (((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real))) ^ 15 := by
      rw [hdiv]
    _ = chenTwoPrimeFactor p ^ 15 *
        (((p ^ alpha : Nat) : Real) *
          ((((p ^ alpha : Nat) : Real) ^ (-1 / 5 : Real)) ^ 15)) := by
      ring
    _ = chenTwoPrimeFactor p ^ 15 *
        (((p ^ alpha : Nat) : Real) *
          ((p ^ alpha : Nat) : Real) ^ (-3 : Real)) := by
      rw [hpow]
    _ = chenTwoPrimeFactor p ^ 15 *
        (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
      rw [hcombine]

/-- The same estimate for the zero-extended coefficient family used by the
singular series. -/
theorem norm_chenTenSingularCoefficientNat_primePow_le_chenTwo
    {p alpha : Nat} [NeZero p] (hp : p.Prime) (hAlpha : 0 < alpha)
    (n : Nat) :
    ‖chenTenSingularCoefficientNat n (p ^ alpha)‖ <=
      chenTwoPrimeFactor p ^ 15 *
        (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  have hpow : p ^ alpha ≠ 0 :=
    pow_ne_zero alpha (NeZero.ne p)
  simp only [chenTenSingularCoefficientNat, dif_neg hpow]
  exact norm_chenTenSingularCoefficient_primePow_le_chenTwo hp hAlpha n

/-- Away from Chen's fixed exceptional set, the local coefficients have the
unit-constant geometric bound. -/
theorem norm_chenTenSingularCoefficientNat_primePow_le_generic
    {p alpha : Nat} [NeZero p] (hp : p.Prime) (hAlpha : 0 < alpha)
    (hmem : p ∉ chenTwoSpecialPrimes) (n : Nat) :
    ‖chenTenSingularCoefficientNat n (p ^ alpha)‖ <=
      (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  simpa [chenTwoPrimeFactor_eq_one_of_not_mem hp hmem] using
    norm_chenTenSingularCoefficientNat_primePow_le_chenTwo hp hAlpha n

end Waring.Analytic
