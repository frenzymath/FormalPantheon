import PrimesRestrictedDigits.Fourier.HybridAuxiliaryBlocks
import PrimesRestrictedDigits.Fourier.HybridLatticeCarrier
import PrimesRestrictedDigits.Fourier.HybridSigmaGrid

/-!
# The Separate Sigma-One Factor

This file bounds the `E'` factor separated before the two squared-block branches in published
Lemma 10.7. See `MAYNARD-PRD-PUBLISHED`, pp. 182--184.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The exact pointwise `Sigma1` sum on a normalized aligned base. -/
noncomputable def decimalHybridSigmaOneAt
    (digit : Fin 10) (length dAux eAux v E : Nat) (x : Real) : Real :=
  ∑ b ∈ alignedGridWindow length (E : Real) x,
    normalizedPaddedDigitFourierMagnitudeAt digit eAux
      ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) *
        ((b : Real) / ((10 ^ length : Nat) : Real)))

/-- The closed shifted upper carrier `0 <= a <= 2E` from the source. -/
noncomputable def decimalHybridSigmaOneShiftedRange
    (digit : Fin 10) (length dAux eAux v E : Nat) (beta : Real) : Real :=
  ∑ a ∈ Finset.range (2 * E + 1),
    normalizedPaddedDigitFourierMagnitudeAt digit eAux
      (beta + (((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) *
        ((a : Real) / ((10 ^ length : Nat) : Real)))

/-- Shifting the least aligned integer embeds the exact closed carrier in
`range (2E+1)`. -/
theorem decimalHybridSigmaOneAt_le_shiftedRange
    (digit : Fin 10) (length dAux eAux v E : Nat) (x : Real)
    (hx : x ∈ Set.Icc (0 : Real) 1) :
    ∃ beta,
      decimalHybridSigmaOneAt digit length dAux eAux v E x <=
        decimalHybridSigmaOneShiftedRange digit length dAux eAux v E beta := by
  classical
  let s := alignedGridWindow length (E : Real) x
  let scale : Real := (((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by dsimp [Y]; positivity
  rcases s.eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨0, ?_⟩
    rw [decimalHybridSigmaOneAt, show alignedGridWindow length (E : Real) x =
      ∅ by simpa only [s] using hempty]
    simp only [Finset.sum_empty]
    exact Finset.sum_nonneg fun a _ =>
      normalizedPaddedDigitFourierMagnitudeAt_nonneg digit eAux _
  · let b0 : Int := s.min' hnonempty
    let offsets : Finset Nat := s.image fun b => (b - b0).toNat
    have hb0 (b : Int) (hb : b ∈ s) : b0 <= b := s.min'_le b hb
    have hdiam (b : Int) (hb : b ∈ s) :
        |(b : Real) - (b0 : Real)| <= 2 * (E : Real) := by
      have hbWindow :=
        (mem_alignedGridWindow_iff_of_mem_Icc (by positivity) hx).mp
          (show b ∈ alignedGridWindow length (E : Real) x by simpa only [s] using hb)
      have hb0Window :=
        (mem_alignedGridWindow_iff_of_mem_Icc (by positivity) hx).mp
          (show b0 ∈ alignedGridWindow length (E : Real) x by
            simpa only [s] using s.min'_mem hnonempty)
      have hdiff :
          |(b : Real) / Y - (b0 : Real) / Y| <=
            2 * ((E : Real) / Y) := by
        calc
          |(b : Real) / Y - (b0 : Real) / Y| =
              |((b : Real) / Y - x) - ((b0 : Real) / Y - x)| := by ring_nf
          _ <= |(b : Real) / Y - x| + |(b0 : Real) / Y - x| :=
            by simpa [abs_sub_comm] using
              (abs_sub_le ((b : Real) / Y - x) 0
                ((b0 : Real) / Y - x))
          _ <= 2 * ((E : Real) / Y) := by
            dsimp [Y] at hbWindow hb0Window ⊢
            linarith
      have hscaled := mul_le_mul_of_nonneg_left hdiff hY.le
      have hleft :
          Y * |(b : Real) / Y - (b0 : Real) / Y| =
            |(b : Real) - (b0 : Real)| := by
        rw [show (b : Real) / Y - (b0 : Real) / Y =
          ((b : Real) - (b0 : Real)) / Y by ring]
        rw [abs_div, abs_of_pos hY]
        field_simp
      rw [hleft] at hscaled
      calc
        |(b : Real) - (b0 : Real)| <=
            Y * (2 * ((E : Real) / Y)) := hscaled
        _ = 2 * (E : Real) := by field_simp
    have hoffNonneg (b : Int) (hb : b ∈ s) : 0 <= b - b0 :=
      sub_nonneg.mpr (hb0 b hb)
    have hoffBound (b : Int) (hb : b ∈ s) :
        (b - b0).toNat <= 2 * E := by
      have hreal : ((b - b0 : Int) : Real) <= (2 * E : Nat) := by
        have habs := hdiam b hb
        rw [abs_of_nonneg (by exact_mod_cast hoffNonneg b hb)] at habs
        exact_mod_cast habs
      have hcast : ((b - b0).toNat : Int) = b - b0 :=
        Int.natCast_toNat_eq_self.mpr (hoffNonneg b hb)
      have hint : b - b0 <= ((2 * E : Nat) : Int) := by
        exact_mod_cast hreal
      have hnatInt : ((b - b0).toNat : Int) <= ((2 * E : Nat) : Int) := by
        rw [hcast]
        exact hint
      exact_mod_cast hnatInt
    have hoffRange (b : Int) (hb : b ∈ s) :
        (b - b0).toNat < 2 * E + 1 := by
      exact Nat.lt_succ_iff.mpr (hoffBound b hb)
    have hoffInjective :
        Set.InjOn (fun b : Int => (b - b0).toNat) (↑s : Set Int) := by
      intro b hb c hc heq
      have hcast : ((b - b0).toNat : Int) = ((c - b0).toNat : Int) := by
        exact_mod_cast heq
      rw [Int.natCast_toNat_eq_self.mpr (hoffNonneg b hb),
        Int.natCast_toNat_eq_self.mpr (hoffNonneg c hc)] at hcast
      omega
    have hsumImage :
        (∑ b ∈ s,
          normalizedPaddedDigitFourierMagnitudeAt digit eAux
            (scale * ((b : Real) / Y))) =
          ∑ a ∈ offsets,
            normalizedPaddedDigitFourierMagnitudeAt digit eAux
              (scale * ((b0 : Real) / Y) + scale * ((a : Real) / Y)) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro b hb
        congr 1
        have hoff := Int.natCast_toNat_eq_self.mpr (hoffNonneg b hb)
        have hbEq : (b : Real) = (b0 : Real) + ((b - b0).toNat : Real) := by
          exact_mod_cast (show b = b0 + (b - b0).toNat by omega)
        rw [hbEq]
        ring
      · exact hoffInjective
    have hoffSubset : offsets ⊆ Finset.range (2 * E + 1) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (hoffRange b hb)
    refine ⟨scale * ((b0 : Real) / Y), ?_⟩
    change (∑ b ∈ s,
        normalizedPaddedDigitFourierMagnitudeAt digit eAux
          (scale * ((b : Real) / Y))) <=
      ∑ a ∈ Finset.range (2 * E + 1),
        normalizedPaddedDigitFourierMagnitudeAt digit eAux
          (scale * ((b0 : Real) / Y) + scale * ((a : Real) / Y))
    rw [hsumImage]
    exact Finset.sum_le_sum_of_subset_of_nonneg hoffSubset fun a _ _ =>
      normalizedPaddedDigitFourierMagnitudeAt_nonneg digit eAux _

private theorem sum_range_mul_grid_le
    (f : Real -> Real) (q M : Nat) (hq : 0 < q) (beta K : Real)
    (hgrid : ∀ gamma,
      (∑ a : Fin q, f (gamma + (a.val : Real) / q)) <= K) :
    (∑ n ∈ Finset.range (M * q),
      f (beta + (n : Real) / q)) <= (M : Real) * K := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hqReal : (q : Real) ≠ 0 := by exact_mod_cast hq.ne'
      have hblock :
          (∑ n ∈ Finset.range q,
            f (beta + ((M * q + n : Nat) : Real) / q)) <= K := by
        calc
          (∑ n ∈ Finset.range q,
              f (beta + ((M * q + n : Nat) : Real) / q)) =
              ∑ n ∈ Finset.range q,
                f ((beta + (M : Real)) + (n : Real) / q) := by
            apply Finset.sum_congr rfl
            intro n hn
            congr 1
            push_cast
            field_simp
            ring
          _ = ∑ a : Fin q,
              f ((beta + (M : Real)) + (a.val : Real) / q) := by
            simpa only using
              (Fin.sum_univ_eq_sum_range
                (fun n : Nat =>
                  f ((beta + (M : Real)) + (n : Real) / q)) q).symm
          _ <= K := hgrid _
      calc
        (∑ n ∈ Finset.range ((Nat.succ M) * q),
            f (beta + (n : Real) / q)) =
            (∑ n ∈ Finset.range (M * q),
              f (beta + (n : Real) / q)) +
              ∑ n ∈ Finset.range q,
                f (beta + ((M * q + n : Nat) : Real) / q) := by
          rw [Nat.succ_mul, Finset.sum_range_add]
        _ <= (M : Real) * K + K := add_le_add ih hblock
        _ = (Nat.succ M : Real) * K := by push_cast; ring

private theorem completeFinGrid_le_twenty_auxiliaryPower
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    (hupper : q <= 10 * 10 ^ length) (beta : Real) :
    (∑ a : Fin q,
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (beta + (a.val : Real) / q)) <=
      20 * largeSieveSamplingConstant *
        (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hqUpper : (q : Real) <= 10 * Y := by
    dsimp [Y]
    exact_mod_cast hupper
  have hsample := completeFinGrid_largeSieveSampling
    digit length q hq (delta := 0) (by norm_num) beta
  have hsample' :
      (∑ a : Fin q,
        normalizedPaddedDigitFourierMagnitudeAt digit length
          (beta + (a.val : Real) / q)) <=
        largeSieveSamplingConstant *
          ((q : Real) ^ largeSieveAlpha +
            (q : Real) * Y ^ (-largeSieveSigma)) := by
    simpa only [closedWindowMaximum_zero
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length),
      zero_mul, zero_add, one_mul, mul_one, Y, add_comm] using hsample
  have htenPower : (10 : Real) ^ largeSieveAlpha <= 10 := by
    calc
      (10 : Real) ^ largeSieveAlpha <= (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by norm_num [largeSieveAlpha])
      _ = 10 := Real.rpow_one 10
  have hhead : (q : Real) ^ largeSieveAlpha <=
      10 * Y ^ largeSieveAlpha := by
    calc
      (q : Real) ^ largeSieveAlpha <=
          (10 * Y) ^ largeSieveAlpha :=
        Real.rpow_le_rpow hq0.le hqUpper largeSieveAlpha_nonneg
      _ = (10 : Real) ^ largeSieveAlpha * Y ^ largeSieveAlpha := by
        rw [Real.mul_rpow (by norm_num : (0 : Real) <= 10) hY.le]
      _ <= 10 * Y ^ largeSieveAlpha :=
        mul_le_mul_of_nonneg_right htenPower
          (Real.rpow_nonneg hY.le _)
  have hcombine : Y * Y ^ (-largeSieveSigma) =
      Y ^ largeSieveAlpha := by
    calc
      Y * Y ^ (-largeSieveSigma) =
          Y ^ (1 : Real) * Y ^ (-largeSieveSigma) := by rw [Real.rpow_one]
      _ = Y ^ ((1 : Real) + (-largeSieveSigma)) :=
        (Real.rpow_add hY _ _).symm
      _ = Y ^ largeSieveAlpha := by
        congr 1
        norm_num [largeSieveAlpha, largeSieveSigma]
  have htail : (q : Real) * Y ^ (-largeSieveSigma) <=
      10 * Y ^ largeSieveAlpha := by
    calc
      (q : Real) * Y ^ (-largeSieveSigma) <=
          (10 * Y) * Y ^ (-largeSieveSigma) :=
        mul_le_mul_of_nonneg_right hqUpper
          (Real.rpow_nonneg hY.le _)
      _ = 10 * Y ^ largeSieveAlpha := by rw [mul_assoc, hcombine]
  have hA : 0 <= largeSieveSamplingConstant := by
    norm_num [largeSieveSamplingConstant]
  have hsum :
      (q : Real) ^ largeSieveAlpha +
          (q : Real) * Y ^ (-largeSieveSigma) <=
        20 * Y ^ largeSieveAlpha := by
    linarith
  calc
    _ <= largeSieveSamplingConstant *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) * Y ^ (-largeSieveSigma)) := hsample'
    _ <= largeSieveSamplingConstant *
        (20 * Y ^ largeSieveAlpha) := by
      exact mul_le_mul_of_nonneg_left hsum hA
    _ = 20 * largeSieveSamplingConstant * Y ^ largeSieveAlpha := by ring

private theorem sigmaOneShiftedRange_le_mul_grid
    (digit : Fin 10) (length dAux eAux v E q M : Nat) (hq : 0 < q)
    (hcount : 2 * E + 1 <= M * q)
    (hstep :
      ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) = 1 / (q : Real))
    (beta K : Real)
    (hgrid : ∀ gamma,
      (∑ a : Fin q,
        normalizedPaddedDigitFourierMagnitudeAt digit eAux
          (gamma + (a.val : Real) / q)) <= K) :
    decimalHybridSigmaOneShiftedRange digit length dAux eAux v E beta <=
      (M : Real) * K := by
  let f : Real -> Real :=
    normalizedPaddedDigitFourierMagnitudeAt digit eAux
  have hqReal : (q : Real) ≠ 0 := by exact_mod_cast hq.ne'
  have hrewrite (a : Nat) :
      ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) *
          ((a : Real) / ((10 ^ length : Nat) : Real))) =
        (a : Real) / q := by
    calc
      (((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) *
          ((a : Real) / ((10 ^ length : Nat) : Real)) =
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) * (a : Real) := by ring
      _ = (1 / (q : Real)) * (a : Real) := by rw [hstep]
      _ = (a : Real) / q := by field_simp
  have hsourceRewrite :
      decimalHybridSigmaOneShiftedRange digit length dAux eAux v E beta =
        ∑ a ∈ Finset.range (2 * E + 1),
          f (beta + (a : Real) / q) := by
    unfold decimalHybridSigmaOneShiftedRange
    apply Finset.sum_congr rfl
    intro a ha
    rw [hrewrite]
  rw [hsourceRewrite]
  calc
    (∑ a ∈ Finset.range (2 * E + 1),
        f (beta + (a : Real) / q)) <=
        ∑ a ∈ Finset.range (M * q),
          f (beta + (a : Real) / q) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hcount) fun a _ _ =>
          normalizedPaddedDigitFourierMagnitudeAt_nonneg digit eAux _
    _ <= (M : Real) * K :=
      sum_range_mul_grid_le f q M hq beta K hgrid

/-- The shifted `Sigma1` range has the source exponent under one uniform
auxiliary loss. -/
theorem decimalHybridSigmaOneShiftedRange_le_source_power
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength : Nat}
    (hscale : dLength + eLength <= length + loss) (beta : Real) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let C : Real := ((10 ^ loss : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    decimalHybridSigmaOneShiftedRange digit length dAux eAux v
        (10 ^ eLength) beta <=
      20 * largeSieveSamplingConstant * (2 * C + 1) *
        E ^ largeSieveAlpha := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let Esource : Nat := 10 ^ eLength
  let Eaux : Nat := 10 ^ eAux
  let Cnat : Nat := 10 ^ loss
  let M : Nat := 2 * Cnat + 1
  let C : Real := (Cnat : Real)
  let E : Real := (Esource : Real)
  change decimalHybridSigmaOneShiftedRange digit length dAux eAux v
      Esource beta <=
    20 * largeSieveSamplingConstant * (2 * C + 1) *
      E ^ largeSieveAlpha
  have hlengths := decimalHybridAuxiliaryLengths_spec hscale
  change dAux <= dLength ∧ dLength <= dAux + loss ∧
    eAux <= eLength ∧ eLength <= eAux + loss ∧
      dAux + eAux <= length at hlengths
  have hpowers := decimalHybridAuxiliaryPowers_data hscale
  change 10 ^ dAux <= 10 ^ dLength ∧
    10 ^ dLength <= 10 ^ loss * 10 ^ dAux ∧
    Eaux <= Esource ∧ Esource <= Cnat * Eaux ∧
      10 ^ dAux * Eaux <= 10 ^ length at hpowers
  have hEauxOne : 1 <= Eaux := by
    dsimp [Eaux]
    exact one_le_pow₀ (by norm_num)
  have hcount : 2 * Esource + 1 <= M * Eaux := by
    calc
      2 * Esource + 1 <= 2 * (Cnat * Eaux) + Eaux :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hpowers.2.2.2.1) hEauxOne
      _ = M * Eaux := by dsimp [M]; ring
  have hparity := decimalHybridSquareScale_power_eq_or_ten_mul
    hlengths.2.2.2.2
  change 10 ^ length = 10 ^ dAux * Eaux * (10 ^ v) ^ 2 ∨
    10 ^ length = 10 * (10 ^ dAux * Eaux * (10 ^ v) ^ 2) at hparity
  have hEauxE : (Eaux : Real) ^ largeSieveAlpha <=
      E ^ largeSieveAlpha := by
    apply Real.rpow_le_rpow (by positivity)
    · dsimp [E]
      exact_mod_cast hpowers.2.2.1
    · exact largeSieveAlpha_nonneg
  have hfinish {q : Nat} (hq : 0 < q) (hcountq : 2 * Esource + 1 <= M * q)
      (hstep :
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) = 1 / (q : Real))
      (hupper : q <= 10 * Eaux) :
      decimalHybridSigmaOneShiftedRange digit length dAux eAux v
          Esource beta <=
        20 * largeSieveSamplingConstant * (2 * C + 1) *
          E ^ largeSieveAlpha := by
    have hgrid (gamma : Real) :=
      completeFinGrid_le_twenty_auxiliaryPower digit eAux q hq
        (by simpa only [Eaux] using hupper) gamma
    have hblocks := sigmaOneShiftedRange_le_mul_grid
      digit length dAux eAux v Esource q M hq hcountq hstep beta
        (20 * largeSieveSamplingConstant *
          (Eaux : Real) ^ largeSieveAlpha) hgrid
    have hM : (M : Real) = 2 * C + 1 := by
      dsimp [M, C, Cnat]
      push_cast
      ring
    have hcoefficient :
        0 <= 20 * largeSieveSamplingConstant * (2 * C + 1) := by
      have hA : 0 <= largeSieveSamplingConstant := by
        norm_num [largeSieveSamplingConstant]
      have hC : 0 <= C := by dsimp [C, Cnat]; positivity
      exact mul_nonneg (mul_nonneg (by norm_num) hA) (by linarith)
    calc
      decimalHybridSigmaOneShiftedRange digit length dAux eAux v
          Esource beta <=
        (M : Real) * (20 * largeSieveSamplingConstant *
          (Eaux : Real) ^ largeSieveAlpha) := hblocks
      _ = 20 * largeSieveSamplingConstant * (2 * C + 1) *
          (Eaux : Real) ^ largeSieveAlpha := by rw [hM]; ring
      _ <= 20 * largeSieveSamplingConstant * (2 * C + 1) *
          E ^ largeSieveAlpha := by
        exact mul_le_mul_of_nonneg_left hEauxE hcoefficient
  have hEauxTen : Eaux <= 10 * Eaux := by omega
  rcases hparity with heq | hten
  · have hstep :
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) = 1 / (Eaux : Real) := by
      have heq' : 10 ^ length =
          ((10 ^ dAux) * (10 ^ v) ^ 2) * Eaux := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using heq
      rw [show ((10 ^ length : Nat) : Real) =
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) * Eaux) by
          exact_mod_cast heq']
      field_simp
    exact hfinish (by dsimp [Eaux]; positivity) hcount hstep hEauxTen
  · let q : Nat := 10 * Eaux
    have hq : 0 < q := by dsimp [q, Eaux]; positivity
    have hcountq : 2 * Esource + 1 <= M * q := by
      exact hcount.trans (Nat.mul_le_mul_left M hEauxTen)
    have hstep :
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) = 1 / (q : Real) := by
      have heq' : 10 ^ length =
          ((10 ^ dAux) * (10 ^ v) ^ 2) * q := by
        dsimp [q]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hten
      rw [show ((10 ^ length : Nat) : Real) =
        ((((10 ^ dAux) * (10 ^ v) ^ 2 : Nat) : Real) * q) by
          exact_mod_cast heq']
      field_simp
    exact hfinish hq hcountq hstep (by rfl)

/-- Uniform pointwise source bound for the separated `Sigma1` factor. -/
theorem decimalHybridSigmaOneAt_le_source_power
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength : Nat}
    (hscale : dLength + eLength <= length + loss)
    (x : Real) (hx : x ∈ Set.Icc (0 : Real) 1) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let C : Real := ((10 ^ loss : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    decimalHybridSigmaOneAt digit length dAux eAux v (10 ^ eLength) x <=
      20 * largeSieveSamplingConstant * (2 * C + 1) *
        E ^ largeSieveAlpha := by
  obtain ⟨beta, hshift⟩ := decimalHybridSigmaOneAt_le_shiftedRange
    digit length
      (decimalHybridAuxiliaryDLength length dLength)
      (decimalHybridAuxiliaryELength length dLength eLength)
      (decimalHybridSquareScaleLength length
        (decimalHybridAuxiliaryDLength length dLength)
        (decimalHybridAuxiliaryELength length dLength eLength))
      (10 ^ eLength) x hx
  exact hshift.trans <|
    decimalHybridSigmaOneShiftedRange_le_source_power
      loss digit hscale beta

end

end PrimesRestrictedDigits
