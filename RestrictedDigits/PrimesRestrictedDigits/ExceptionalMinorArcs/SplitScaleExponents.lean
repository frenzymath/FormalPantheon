import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitProductScales

/-!
# Exponent margins for the two product scales

This turns the canonical factor-ten loss into the exact exponent `1 / length` and proves both
convenient-scale branches.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- At decimal ambient scale, one factor ten is exactly the real-power
increment `1/length`. -/
theorem decimalScale_rpow_one_div_length
    {length : Nat} (hlength : 0 < length) :
    (((10 ^ length : Nat) : Real) ^ (1 / (length : Real))) = 10 := by
  have hlengthReal : (length : Real) ≠ 0 := by exact_mod_cast hlength.ne'
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : Real) <= 10)]
  have hcancel : (length : Real) * (1 / (length : Real)) = 1 := by
    field_simp
  rw [hcancel, Real.rpow_one]

/-- Multiplication by ten adds exactly `1/length` to a decimal-scale
exponent. -/
theorem ten_mul_decimalScale_rpow
    {length : Nat} (hlength : 0 < length) (z : Real) :
    10 * (((10 ^ length : Nat) : Real) ^ z) =
      (((10 ^ length : Nat) : Real) ^
        (z + 1 / (length : Real))) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by dsimp only [X]; positivity
  calc
    10 * X ^ z = X ^ (1 / (length : Real)) * X ^ z := by
      rw [decimalScale_rpow_one_div_length hlength]
    _ = X ^ (1 / (length : Real) + z) :=
      (Real.rpow_add hX _ _).symm
    _ = X ^ (z + 1 / (length : Real)) := by ring_nf

/-- The selected canonical product scale is convenient in the first source
subset-sum interval. -/
theorem selectedFactorTenScale_mem_bilinearRange
    {length k n : Nat} {a : Fin k -> Real} {delta mu : Real}
    {I : Finset (Fin k)}
    (hlength : 0 < length) (hdelta : 0 <= delta)
    (hmargin : ((k + 1 : Nat) : Real) * delta +
      1 / (length : Real) <= mu)
    (ht : (∑ i ∈ I, a i) ∈
      Set.Icc (9 / 25 + mu) (17 / 40 - mu))
    (hweight : selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I n ≠ 0) :
    (((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) <=
        (factorTenScale n : Real) ∧
      (factorTenScale n : Real) <=
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let t : Real := ∑ i ∈ I, a i
  change 9 / 25 + mu <= t ∧ t <= 17 / 40 - mu at ht
  have hlengthReal : (0 : Real) < length := by exact_mod_cast hlength
  have hinvLength : (0 : Real) < 1 / (length : Real) := by positivity
  have hellDelta : 0 <= ((k + 1 : Nat) : Real) * delta := by positivity
  have hmu : 0 <= mu := by linarith
  have hXOne : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlength.ne' (by norm_num : 1 < 10)
  have hsupport := selectedProjectedPrimeWeightAtProduct_support
    (X := 10 ^ length) (n := n) (a := a) (delta := delta) (I := I)
    (Nat.one_lt_pow hlength.ne' (by norm_num)) hweight
  have hnPosReal : (0 : Real) < n :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hXOne) t).trans_le hsupport.1
  have hnPos : 0 < n := by exact_mod_cast hnPosReal
  have hband := factorTenScale_band n hnPos
  have hscaleUpper : (factorTenScale n : Real) < 10 * (n : Real) := by
    exact_mod_cast factorTenScale_lt_ten_mul hnPos
  have hcard : (I.card : Real) <= ((k + 1 : Nat) : Real) := by
    have hcardNat : I.card <= k := by simpa using I.card_le_univ
    exact_mod_cast hcardNat.trans (Nat.le_succ k)
  have hcardDelta : (I.card : Real) * delta <=
      ((k + 1 : Nat) : Real) * delta :=
    mul_le_mul_of_nonneg_right hcard hdelta
  have hexponentUpper :
      t + (I.card : Real) * delta + 1 / (length : Real) <= 17 / 40 := by
    dsimp only [t] at ht ⊢
    linarith
  refine ⟨?_, ?_⟩
  · calc
      X ^ (9 / 25 : Real) <= X ^ t :=
        Real.rpow_le_rpow_of_exponent_le hXOne.le (by linarith)
      _ <= (n : Real) := by simpa only [X, t] using hsupport.1
      _ <= (factorTenScale n : Real) := hband.2
  · exact (calc
      (factorTenScale n : Real) < 10 * (n : Real) := hscaleUpper
      _ <= 10 * X ^ (t + (I.card : Real) * delta) := by
        gcongr
        simpa only [X, t] using hsupport.2
      _ = X ^ (t + (I.card : Real) * delta +
          1 / (length : Real)) := by
        simpa only [X] using
          ten_mul_decimalScale_rpow hlength
            (t + (I.card : Real) * delta)
      _ <= X ^ (17 / 40 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hXOne.le hexponentUpper).le

/-- The complementary-plus-last canonical product scale is convenient in the
second source subset-sum interval, using the active product cutoff. -/
theorem complementaryFactorTenScale_mem_bilinearRange
    {length k n m : Nat} {a : Fin k -> Real} {delta mu eta : Real}
    {I : Finset (Fin k)}
    (hlength : 0 < length) (hdelta : 0 <= delta)
    (hmargin : ((k + 1 : Nat) : Real) * delta +
      1 / (length : Real) <= mu)
    (ht : (∑ i ∈ I, a i) ∈
      Set.Icc (23 / 40 + mu) (16 / 25 - mu))
    (hselected : selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I n ≠ 0)
    (hcomplementary : complementaryLastPrimeWeightAtProduct
      (10 ^ length) a delta eta I m ≠ 0)
    (hnm : n * m < 10 ^ length) :
    (((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) <=
        (factorTenScale m : Real) ∧
      (factorTenScale m : Real) <=
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let t : Real := ∑ i ∈ I, a i
  change 23 / 40 + mu <= t ∧ t <= 16 / 25 - mu at ht
  have hlengthReal : (0 : Real) < length := by exact_mod_cast hlength
  have hinvLength : (0 : Real) < 1 / (length : Real) := by positivity
  have hellDelta : 0 <= ((k + 1 : Nat) : Real) * delta := by positivity
  have hmu : 0 <= mu := by linarith
  have hXOne : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlength.ne' (by norm_num : 1 < 10)
  have hselectedSupport := selectedProjectedPrimeWeightAtProduct_support
    (X := 10 ^ length) (n := n) (a := a) (delta := delta) (I := I)
    (Nat.one_lt_pow hlength.ne' (by norm_num)) hselected
  have hcomplementarySupport :=
    complementaryLastPrimeWeightAtProduct_lower_support
      (X := 10 ^ length) (m := m) (a := a) (delta := delta)
      (eta := eta) (I := I)
      (Nat.one_lt_pow hlength.ne' (by norm_num)) hcomplementary
  have hnPosReal : (0 : Real) < n :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hXOne) t).trans_le
      hselectedSupport.1
  have hmPosReal : (0 : Real) < m :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hXOne)
      (1 - t - ((k + 1 : Nat) : Real) * delta)).trans_le
        hcomplementarySupport
  have hnPos : 0 < n := by exact_mod_cast hnPosReal
  have hmPos : 0 < m := by exact_mod_cast hmPosReal
  have hmBand := factorTenScale_band m hmPos
  have hmScaleUpper : (factorTenScale m : Real) < 10 * (m : Real) := by
    exact_mod_cast factorTenScale_lt_ten_mul hmPos
  have hexponentLower : (9 / 25 : Real) <=
      1 - t - ((k + 1 : Nat) : Real) * delta := by
    linarith
  have hinvLeMu : 1 / (length : Real) <= mu := by linarith
  have hexponentUpper :
      1 - t + 1 / (length : Real) <= 17 / 40 := by
    linarith
  have hnmReal : (n : Real) * (m : Real) < X := by
    dsimp only [X]
    exact_mod_cast hnm
  have hmUpper : (m : Real) < X ^ (1 - t) := by
    rw [Real.rpow_sub (zero_lt_one.trans hXOne), Real.rpow_one]
    apply (lt_div_iff₀ (Real.rpow_pos_of_pos
      (zero_lt_one.trans hXOne) t)).2
    calc
      (m : Real) * X ^ t = X ^ t * (m : Real) := by ring
      _ <= (n : Real) * (m : Real) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [X, t] using hselectedSupport.1) (by positivity)
      _ < X := hnmReal
  refine ⟨?_, ?_⟩
  · calc
      X ^ (9 / 25 : Real) <=
          X ^ (1 - t - ((k + 1 : Nat) : Real) * delta) :=
        Real.rpow_le_rpow_of_exponent_le hXOne.le hexponentLower
      _ <= (m : Real) := by
        simpa only [X, t] using hcomplementarySupport
      _ <= (factorTenScale m : Real) := hmBand.2
  · exact (calc
      (factorTenScale m : Real) < 10 * (m : Real) := hmScaleUpper
      _ < 10 * X ^ (1 - t) := by gcongr
      _ = X ^ (1 - t + 1 / (length : Real)) := by
        simpa only [X] using
          ten_mul_decimalScale_rpow hlength (1 - t)
      _ <= X ^ (17 / 40 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hXOne.le hexponentUpper).le

/-- Active selected and complementary scales satisfy the stronger strict
product bound used by the repaired reduction. -/
theorem activeSplitFactorTenScales_mul_lt
    {length k n m : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)}
    (hlength : 0 < length)
    (hselected : selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I n ≠ 0)
    (hcomplementary : complementaryLastPrimeWeightAtProduct
      (10 ^ length) a delta eta I m ≠ 0)
    (hnm : n * m < 10 ^ length) :
    (factorTenScale n : Real) * (factorTenScale m : Real) <
      100 * (((10 ^ length : Nat) : Real)) := by
  have hX := Nat.one_lt_pow hlength.ne' (by norm_num : 1 < 10)
  have hnSupport := selectedProjectedPrimeWeightAtProduct_support
    (X := 10 ^ length) (n := n) (a := a) (delta := delta) (I := I)
    hX hselected
  have hmSupport := complementaryLastPrimeWeightAtProduct_lower_support
    (X := 10 ^ length) (m := m) (a := a) (delta := delta)
    (eta := eta) (I := I) hX hcomplementary
  have hnPosReal : (0 : Real) < n :=
    (Real.rpow_pos_of_pos (by positivity)
      (∑ i ∈ I, a i)).trans_le hnSupport.1
  have hmPosReal : (0 : Real) < m :=
    (Real.rpow_pos_of_pos (by positivity)
      (1 - (∑ i ∈ I, a i) - ((k + 1 : Nat) : Real) * delta)).trans_le
        hmSupport
  exact factorTenScales_mul_lt_hundred_mul
    (by exact_mod_cast hnPosReal) (by exact_mod_cast hmPosReal) hnm

/-- One of the two canonical scales is in the convenient bilinear range
under the source's two subset-sum alternatives. -/
theorem splitFactorTenScale_convenient_dichotomy
    {length k n m : Nat} {a : Fin k -> Real} {delta mu eta : Real}
    {I : Finset (Fin k)}
    (hlength : 0 < length) (hdelta : 0 <= delta)
    (hmargin : ((k + 1 : Nat) : Real) * delta +
      1 / (length : Real) <= mu)
    (ht : (∑ i ∈ I, a i) ∈
        Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
      (∑ i ∈ I, a i) ∈
        Set.Icc (23 / 40 + mu) (16 / 25 - mu))
    (hselected : selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I n ≠ 0)
    (hcomplementary : complementaryLastPrimeWeightAtProduct
      (10 ^ length) a delta eta I m ≠ 0)
    (hnm : n * m < 10 ^ length) :
    ((((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) <=
        (factorTenScale n : Real) ∧
      (factorTenScale n : Real) <=
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real))) ∨
      ((((10 ^ length : Nat) : Real) ^ (9 / 25 : Real)) <=
        (factorTenScale m : Real) ∧
      (factorTenScale m : Real) <=
        (((10 ^ length : Nat) : Real) ^ (17 / 40 : Real))) := by
  rcases ht with ht | ht
  · exact Or.inl <| selectedFactorTenScale_mem_bilinearRange
      hlength hdelta hmargin ht hselected
  · exact Or.inr <| complementaryFactorTenScale_mem_bilinearRange
      hlength hdelta hmargin ht hselected hcomplementary hnm

end

end PrimesRestrictedDigits
