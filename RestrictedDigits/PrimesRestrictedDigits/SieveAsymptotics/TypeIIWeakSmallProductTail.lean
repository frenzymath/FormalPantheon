import PrimesRestrictedDigits.Foundations.PowerLaw
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTailScalars

/-!
# Type II weak small-product tails

This file proves the two raw carrier estimates in Eq. (9.4), including the weak cutoff,
excluded-zero semantics, and the ambient zero term.
-/

namespace PrimesRestrictedDigits

noncomputable section

private noncomputable def typeIIWeakTailExponent : Real :=
  Real.log (9 : Real) / Real.log (10 : Real)

private theorem typeIIWeakTailExponent_pos :
    0 < typeIIWeakTailExponent := by
  simpa only [typeIIWeakTailExponent] using
    typeIIWeakSmallProductExponent_pos_lt_one.1

private theorem typeIIWeakTailExponent_le_one :
    typeIIWeakTailExponent ≤ 1 := by
  exact typeIIWeakSmallProductExponent_pos_lt_one.2.le

/-- At positive fixed length, padded omission implies standard omission for
all excluded digits, including zero. -/
theorem paddedOmitsDecimalDigit_imp_omitsDecimalDigit_of_pos_length
    {digit : Fin 10} {length n : Nat} (hlength : 0 < length)
    (h : paddedOmitsDecimalDigit digit length n) :
    omitsDecimalDigit digit n := by
  rw [omitsDecimalDigit_iff]
  intro ha
  by_cases hn : n = 0
  · subst n
    simp only [standardDecimalDigits_zero, List.mem_singleton] at ha
    have ha0 : digit = (0 : Fin 10) := Fin.ext ha
    subst digit
    have hzero := (paddedZero_omitsZero_iff length).mp h
    omega
  · rw [standardDecimalDigits_eq_digits hn] at ha
    unfold paddedOmitsDecimalDigit at h
    apply h
    rw [paddedDecimalDigits, Nat.digitsAppend]
    exact List.mem_append_left _ ha

/-- Difference from the strict near carrier is exactly the weak lower tail
inside any carrier below `X`. -/
theorem sdiff_typeIINearXCarrier_eq_filter_le
    (C : Finset Nat) {X : Nat} (delta : Real)
    (hC : C ⊆ Finset.range X) :
    C \ typeIINearXCarrier X delta =
      C.filter (fun n : Nat => (n : Real) ≤
        (X : Real) ^ (1 - delta ^ 2)) := by
  classical
  ext n
  rw [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hnC, hnNear⟩
    refine ⟨hnC, ?_⟩
    have hnX : n < X := Finset.mem_range.mp (hC hnC)
    by_contra hnle
    have hlt : (X : Real) ^ (1 - delta ^ 2) < (n : Real) :=
      lt_of_not_ge hnle
    exact hnNear (mem_typeIINearXCarrier.mpr ⟨hnX, hlt⟩)
  · rintro ⟨hnC, hnle⟩
    refine ⟨hnC, ?_⟩
    intro hnNear
    exact (not_lt_of_ge hnle) (mem_typeIINearXCarrier.mp hnNear).2

private theorem card_paddedRestrictedNumbers_sdiff_near_le_restrictedCount
    {digit : Fin 10} {length : Nat} (hlength : 0 < length)
    (delta : Real) :
    (paddedRestrictedNumbers digit length \
        typeIINearXCarrier (10 ^ length) delta).card ≤
      restrictedCount digit
        ((((10 ^ length : Nat) : Real) ^ (1 - delta ^ 2)) + 1) := by
  classical
  rw [restrictedCount]
  apply Finset.card_le_card
  intro n hn
  rcases Finset.mem_sdiff.mp hn with ⟨hnA, hnNear⟩
  rcases mem_paddedRestrictedNumbers.mp hnA with ⟨hnX, hnOmit⟩
  have hnLe : (n : Real) ≤
      ((10 ^ length : Nat) : Real) ^ (1 - delta ^ 2) := by
    by_contra hnle
    have hlt : ((10 ^ length : Nat) : Real) ^ (1 - delta ^ 2) <
        (n : Real) := lt_of_not_ge hnle
    exact hnNear (mem_typeIINearXCarrier.mpr ⟨hnX, hlt⟩)
  rw [mem_restrictedNumbers]
  exact ⟨by linarith,
    paddedOmitsDecimalDigit_imp_omitsDecimalDigit_of_pos_length
      hlength hnOmit⟩

private theorem powTen_rpow_exponent_lt_hundred_mul_paddedCard
    (digit : Fin 10) (length : Nat)
    (hX : 4 ≤ ((10 ^ length : Nat) : Real)) :
    ((10 ^ length : Nat) : Real) ^ typeIIWeakTailExponent <
      100 * ((paddedRestrictedNumbers digit length).card : Real) := by
  have hcount :=
    (restrictedCount_rpow_comparable (a := (1 : Fin 10)) hX).1
  have hcard :
      (restrictedCount (1 : Fin 10) ((10 ^ length : Nat) : Real) : Real) =
        ((paddedRestrictedNumbers digit length).card : Real) := by
    rw [restrictedCount,
      restrictedNumbers_eq_paddedRestrictedNumbers_of_ne_zero
        (by norm_num : (1 : Fin 10).val ≠ 0),
      card_paddedRestrictedNumbers, card_paddedRestrictedNumbers]
  rw [hcard] at hcount
  change (1 / 100 : Real) *
      ((10 ^ length : Nat) : Real) ^ typeIIWeakTailExponent <
    ((paddedRestrictedNumbers digit length).card : Real) at hcount
  nlinarith

private theorem paddedRestrictedNumbers_sdiff_near_le
    (digit : Fin 10) {length : Nat} (hlength : 0 < length)
    (delta : Real)
    (hX : 9 ≤ ((10 ^ length : Nat) : Real))
    (hY : 3 ≤ ((10 ^ length : Nat) : Real) ^ (1 - delta ^ 2)) :
    ((paddedRestrictedNumbers digit length \
        typeIINearXCarrier (10 ^ length) delta).card : Real) ≤
      20000 * ((paddedRestrictedNumbers digit length).card : Real) /
        ((10 ^ length : Nat) : Real) ^
          (typeIIWeakTailExponent * delta ^ 2) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let Y : Real := X ^ (1 - delta ^ 2)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let tail : Finset Nat := A \ typeIINearXCarrier (10 ^ length) delta
  have hXPos : 0 < X := by linarith
  have hXFour : 4 ≤ X := by linarith
  have hYPos : 0 < Y := by linarith
  have hcardNat : tail.card ≤ restrictedCount digit (Y + 1) := by
    simpa only [tail, A, Y, X] using
      card_paddedRestrictedNumbers_sdiff_near_le_restrictedCount
        hlength delta
  have hcard : (tail.card : Real) ≤ (restrictedCount digit (Y + 1) : Real) := by
    exact_mod_cast hcardNat
  have hcount : (restrictedCount digit (Y + 1) : Real) <
      100 * (Y + 1) ^ typeIIWeakTailExponent := by
    have := (restrictedCount_rpow_comparable (a := digit)
      (by linarith : 4 ≤ Y + 1)).2
    simpa only [typeIIWeakTailExponent] using this
  have hYTwo : Y + 1 ≤ 2 * Y := by linarith
  have htwoRpow : (2 : Real) ^ typeIIWeakTailExponent ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2)
        typeIIWeakTailExponent_le_one
  have hYPlusRpow : (Y + 1) ^ typeIIWeakTailExponent ≤
      2 * Y ^ typeIIWeakTailExponent := by
    calc
      (Y + 1) ^ typeIIWeakTailExponent ≤
          (2 * Y) ^ typeIIWeakTailExponent :=
        Real.rpow_le_rpow (by positivity) hYTwo
          typeIIWeakTailExponent_pos.le
      _ = (2 : Real) ^ typeIIWeakTailExponent *
          Y ^ typeIIWeakTailExponent :=
        Real.mul_rpow (by norm_num) hYPos.le
      _ ≤ 2 * Y ^ typeIIWeakTailExponent :=
        mul_le_mul_of_nonneg_right htwoRpow
          (Real.rpow_nonneg hYPos.le _)
  have htailY : (tail.card : Real) ≤
      200 * Y ^ typeIIWeakTailExponent := by
    calc
      (tail.card : Real) ≤ (restrictedCount digit (Y + 1) : Real) := hcard
      _ ≤ 100 * (Y + 1) ^ typeIIWeakTailExponent := hcount.le
      _ ≤ 100 * (2 * Y ^ typeIIWeakTailExponent) :=
        mul_le_mul_of_nonneg_left hYPlusRpow (by norm_num)
      _ = 200 * Y ^ typeIIWeakTailExponent := by ring
  have hYPower : Y ^ typeIIWeakTailExponent =
      X ^ typeIIWeakTailExponent /
        X ^ (typeIIWeakTailExponent * delta ^ 2) := by
    dsimp only [Y]
    calc
      (X ^ (1 - delta ^ 2)) ^ typeIIWeakTailExponent =
          X ^ ((1 - delta ^ 2) * typeIIWeakTailExponent) :=
        (Real.rpow_mul hXPos.le _ _).symm
      _ = X ^ (typeIIWeakTailExponent -
          typeIIWeakTailExponent * delta ^ 2) := by
        congr 1
        ring
      _ = X ^ typeIIWeakTailExponent /
          X ^ (typeIIWeakTailExponent * delta ^ 2) :=
        Real.rpow_sub hXPos _ _
  have hXPower : X ^ typeIIWeakTailExponent <
      100 * (A.card : Real) := by
    simpa only [X, A] using
      powTen_rpow_exponent_lt_hundred_mul_paddedCard digit length hXFour
  have hdenNonneg :
      0 ≤ X ^ (typeIIWeakTailExponent * delta ^ 2) :=
    Real.rpow_nonneg hXPos.le _
  change (tail.card : Real) ≤
    20000 * (A.card : Real) /
      X ^ (typeIIWeakTailExponent * delta ^ 2)
  calc
    (tail.card : Real) ≤ 200 * Y ^ typeIIWeakTailExponent := htailY
    _ = 200 * (X ^ typeIIWeakTailExponent /
        X ^ (typeIIWeakTailExponent * delta ^ 2)) := by rw [hYPower]
    _ ≤ 200 * ((100 * (A.card : Real)) /
        X ^ (typeIIWeakTailExponent * delta ^ 2)) := by
      gcongr
    _ = 20000 * (A.card : Real) /
        X ^ (typeIIWeakTailExponent * delta ^ 2) := by ring

private theorem maynardAmbientCarrier_sdiff_near_le
    (digit : Fin 10) {length : Nat} (delta : Real)
    (hX : 9 ≤ ((10 ^ length : Nat) : Real))
    (hY : 3 ≤ ((10 ^ length : Nat) : Real) ^ (1 - delta ^ 2)) :
    (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real) *
        (((maynardAmbientCarrier ((10 ^ length : Nat) : Real) \
          typeIINearXCarrier (10 ^ length) delta).card : Real)) ≤
      3 * ((paddedRestrictedNumbers digit length).card : Real) /
        ((10 ^ length : Nat) : Real) ^
          (typeIIWeakTailExponent * delta ^ 2) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let Y : Real := X ^ (1 - delta ^ 2)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let tail : Finset Nat := B \ typeIINearXCarrier XNat delta
  let rho : Real := restrictedDigitDensity digit
  have hXPos : 0 < X := by linarith
  have hXOne : 1 ≤ X := hX.trans' (by norm_num)
  have hYPos : 0 < Y := by linarith
  have htailNat : tail.card ≤ Nat.floor Y + 1 := by
    rw [← Finset.card_range (Nat.floor Y + 1)]
    apply Finset.card_le_card
    intro n hn
    rcases Finset.mem_sdiff.mp hn with ⟨hnB, hnNear⟩
    have hnX : n < XNat := by
      dsimp only [B] at hnB
      rw [maynardAmbientCarrier_natCast] at hnB
      exact Finset.mem_range.mp hnB
    have hnLe : (n : Real) ≤ Y := by
      by_contra hnle
      exact hnNear (mem_typeIINearXCarrier.mpr
        ⟨hnX, lt_of_not_ge hnle⟩)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hnLe))
  have htailCast : (tail.card : Real) ≤ Y + 1 := by
    calc
      (tail.card : Real) ≤ ((Nat.floor Y + 1 : Nat) : Real) := by
        exact_mod_cast htailNat
      _ = (Nat.floor Y : Real) + 1 := by norm_num
      _ ≤ Y + 1 := by
        simpa only [add_comm] using
          add_le_add_right (Nat.floor_le hYPos.le) 1
  have htailTwo : (tail.card : Real) ≤ 2 * Y :=
    htailCast.trans (by linarith)
  have hrhoNonneg : 0 ≤ rho := by
    simpa only [rho] using restrictedDigitDensity_nonneg digit
  have hrhoUpper : rho ≤ 10 / 9 := by
    simpa only [rho] using restrictedDigitDensity_le_ten_ninths digit
  have hAcardNonneg : 0 ≤ (A.card : Real) := by positivity
  have hcoeffNonneg : 0 ≤ rho * (A.card : Real) / X :=
    div_nonneg (mul_nonneg hrhoNonneg hAcardNonneg) hXPos.le
  have hbaseNonneg : 0 ≤ (A.card : Real) * Y / X := by positivity
  have htwentyNinths : (10 / 9 : Real) * 2 ≤ 3 := by norm_num
  have hcrude : rho * (A.card : Real) / X * (tail.card : Real) ≤
      3 * ((A.card : Real) * Y / X) := by
    calc
      rho * (A.card : Real) / X * (tail.card : Real) ≤
          rho * (A.card : Real) / X * (2 * Y) :=
        mul_le_mul_of_nonneg_left htailTwo hcoeffNonneg
      _ = rho * (2 * ((A.card : Real) * Y / X)) := by ring
      _ ≤ (10 / 9 : Real) *
          (2 * ((A.card : Real) * Y / X)) :=
        mul_le_mul_of_nonneg_right hrhoUpper (by positivity)
      _ = ((10 / 9 : Real) * 2) * ((A.card : Real) * Y / X) := by ring
      _ ≤ 3 * ((A.card : Real) * Y / X) :=
        mul_le_mul_of_nonneg_right htwentyNinths hbaseNonneg
  have hYdivX : Y / X = 1 / X ^ (delta ^ 2) := by
    dsimp only [Y]
    rw [Real.rpow_sub hXPos, Real.rpow_one]
    field_simp [hXPos.ne']
  have hexponentLe : typeIIWeakTailExponent * delta ^ 2 ≤ delta ^ 2 := by
    nlinarith [typeIIWeakTailExponent_le_one, sq_nonneg delta,
      typeIIWeakTailExponent_pos.le]
  have hdenLe : X ^ (typeIIWeakTailExponent * delta ^ 2) ≤
      X ^ (delta ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hXOne hexponentLe
  have hinvLe : 1 / X ^ (delta ^ 2) ≤
      1 / X ^ (typeIIWeakTailExponent * delta ^ 2) :=
    one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hXPos _ ) hdenLe
  change rho * (A.card : Real) / X * (tail.card : Real) ≤
    3 * (A.card : Real) /
      X ^ (typeIIWeakTailExponent * delta ^ 2)
  calc
    rho * (A.card : Real) / X * (tail.card : Real) ≤
        3 * ((A.card : Real) * Y / X) := hcrude
    _ = 3 * (A.card : Real) * (Y / X) := by ring
    _ = 3 * (A.card : Real) * (1 / X ^ (delta ^ 2)) := by rw [hYdivX]
    _ ≤ 3 * (A.card : Real) *
        (1 / X ^ (typeIIWeakTailExponent * delta ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hinvLe (by positivity)
    _ = 3 * (A.card : Real) /
        X ^ (typeIIWeakTailExponent * delta ^ 2) := by ring

/-- The combined weak small-product tails in Eq. (9.4), uniformly in the
excluded decimal digit. -/
theorem exists_typeIIWeakSmallProductTail_upper :
    ∃ Ctail : Real, 0 < Ctail ∧
      ∃ length0 : Nat, 1 ≤ length0 ∧
        ∀ length : Nat, length0 ≤ length →
        ∀ digit : Fin 10,
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let delta : Real := majorArcM2LogLogDelta XNat
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let near : Finset Nat := typeIINearXCarrier XNat delta
          (((A \ near).card : Real) +
              (restrictedDigitDensity digit : Real) *
                (A.card : Real) / X * (((B \ near).card : Real))) ≤
            Ctail * delta * (A.card : Real) / Real.log X := by
  obtain ⟨length0, hlength0, hscale⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨20003, by norm_num, length0, hlength0, ?_⟩
  intro length hlength digit
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let near : Finset Nat := typeIINearXCarrier XNat delta
  have hlengthPos : 0 < length := by
    omega
  have hscaleAt := hscale length hlength
  have hrestricted : ((A \ near).card : Real) ≤
      20000 * (A.card : Real) /
        X ^ (typeIIWeakTailExponent * delta ^ 2) := by
    simpa only [A, near, X, XNat, delta] using
      paddedRestrictedNumbers_sdiff_near_le digit hlengthPos delta
        hscaleAt.1 hscaleAt.2.2.2.1
  have hambient :
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
          (((B \ near).card : Real)) ≤
        3 * (A.card : Real) /
          X ^ (typeIIWeakTailExponent * delta ^ 2) := by
    simpa only [A, B, near, X, XNat, delta] using
      maynardAmbientCarrier_sdiff_near_le digit delta
        hscaleAt.1 hscaleAt.2.2.2.1
  have hsum :
      ((A \ near).card : Real) +
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
            (((B \ near).card : Real)) ≤
        20003 * (A.card : Real) /
          X ^ (typeIIWeakTailExponent * delta ^ 2) := by
    calc
      ((A \ near).card : Real) +
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
            (((B \ near).card : Real)) ≤
          20000 * (A.card : Real) /
              X ^ (typeIIWeakTailExponent * delta ^ 2) +
            3 * (A.card : Real) /
              X ^ (typeIIWeakTailExponent * delta ^ 2) :=
        add_le_add hrestricted hambient
      _ = 20003 * (A.card : Real) /
          X ^ (typeIIWeakTailExponent * delta ^ 2) := by ring
  have hscalar :
      1 / X ^ (typeIIWeakTailExponent * delta ^ 2) ≤
        delta / Real.log X := by
    simpa only [typeIIWeakTailExponent, X, XNat, delta] using
      hscaleAt.2.2.2.2.2
  calc
    ((A \ near).card : Real) +
        (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
          (((B \ near).card : Real)) ≤
      20003 * (A.card : Real) /
        X ^ (typeIIWeakTailExponent * delta ^ 2) := hsum
    _ = (20003 * (A.card : Real)) *
        (1 / X ^ (typeIIWeakTailExponent * delta ^ 2)) := by ring
    _ ≤ (20003 * (A.card : Real)) * (delta / Real.log X) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = 20003 * delta * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
