import PrimesRestrictedDigits.Fourier.HybridLatticeCarrier
import PrimesRestrictedDigits.Fourier.FirstMomentL1
import PrimesRestrictedDigits.Fourier.LargeSieveScaleLoss

/-!
# Consecutive shifted decimal grids

This module supplies the tail estimate in the sparse branch.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem sum_range_shifted_firstMoment_le
    (digit : Fin 10) (length : Nat) (beta : Real) :
    (∑ n ∈ Finset.range (10 ^ length),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (beta + (n : Real) / ((10 ^ length : Nat) : Real))) <=
      20000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by
  have h := firstMomentShiftedFrequencySum_le digit length beta
  have h' :
      (∑ n ∈ Finset.range (10 ^ length),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          (beta + (n : Real) / ((10 ^ length : Nat) : Real))) <=
        20000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by
    simpa only [← Fin.sum_univ_eq_sum_range, Nat.cast_pow, Nat.cast_ofNat,
      add_comm, largeSieveAlpha] using h
  exact h'

private theorem sum_range_four_shiftedBlocks_le
    (digit : Fin 10) (length : Nat) (beta : Real) :
    (∑ n ∈ Finset.range (4 * 10 ^ length),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (beta + (n : Real) / ((10 ^ length : Nat) : Real))) <=
      80000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by
  let N : Nat := 10 ^ length
  let f : Nat -> Real := fun n =>
    normalizedPaddedDigitFourierMagnitudeAt digit length
      (beta + (n : Real) / (N : Real))
  have hblock (k : Nat) :
      (∑ n ∈ Finset.range N, f (k * N + n)) <=
        20000 * (N : Real) ^ largeSieveAlpha := by
    have h := sum_range_shifted_firstMoment_le digit length
      (beta + (k : Real))
    calc
      (∑ n ∈ Finset.range N, f (k * N + n)) =
          ∑ n ∈ Finset.range N,
            normalizedPaddedDigitFourierMagnitudeAt digit length
              (beta + (k : Real) + (n : Real) / (N : Real)) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [f]
        congr 1
        push_cast
        field_simp [show (N : Real) ≠ 0 by positivity]
        ring
      _ <= 20000 * (N : Real) ^ largeSieveAlpha := by
        simpa only [N] using h
  have hsplit :
      (∑ n ∈ Finset.range (4 * N), f n) =
        (∑ n ∈ Finset.range N, f n) +
          (∑ n ∈ Finset.range N, f (N + n)) +
          (∑ n ∈ Finset.range N, f (2 * N + n)) +
          (∑ n ∈ Finset.range N, f (3 * N + n)) := by
    rw [show 4 * N = N + (N + (N + N)) by omega,
      Finset.sum_range_add]
    rw [show 3 * N = N + (N + N) by omega,
      Finset.sum_range_add]
    rw [show 2 * N = N + N by omega,
      Finset.sum_range_add]
    simp only [Nat.add_assoc]
    ring
  rw [hsplit]
  have h0 := hblock 0
  have h1 := hblock 1
  have h2 := hblock 2
  have h3 := hblock 3
  simp only [zero_mul, zero_add, one_mul] at h0 h1 h2 h3
  have hN : (N : Real) ^ largeSieveAlpha =
      (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by rfl
  rw [hN] at h0 h1 h2 h3 ⊢
  linarith

/-- A closed aligned window contributes at most four complete tail grids when
the tail scale is at least the window parameter. -/
theorem alignedGridWindow_tail_sum_le
    (digit : Fin 10) (length w : Nat) (E x : Real)
    (hE : 1 <= E) (hW : E <= ((10 ^ w : Nat) : Real))
    (hWUpper : ((10 ^ w : Nat) : Real) < 100 * E) :
    (∑ b ∈ alignedGridWindow length E x,
      normalizedPaddedDigitFourierMagnitudeAt digit w
        ((b : Real) / ((10 ^ w : Nat) : Real))) <=
      8000000 * (E ^ largeSieveAlpha) := by
  let s := alignedGridWindow length E x
  let N : Nat := 10 ^ w
  let W : Real := (N : Real)
  by_cases hs : s.Nonempty
  · let b0 : Int := s.min' hs
    let offsets : Finset Nat := s.image fun b => (b - b0).toNat
    have hb0 (b : Int) (hb : b ∈ s) : b0 <= b := by
      exact s.min'_le b hb
    have hdiam (b : Int) (hb : b ∈ s) :
        |(b : Real) - (b0 : Real)| <= 2 * E := by
      have hb' := (mem_alignedGridWindow_iff.mp hb).2.2
      have hb0' := (mem_alignedGridWindow_iff.mp (s.min'_mem hs)).2.2
      let Y : Real := ((10 ^ length : Nat) : Real)
      have hY : 0 < Y := by
        dsimp [Y]
        positivity
      have hsum :
          |(b : Real) / Y - x| + |(b0 : Real) / Y - x| <=
            2 * (E / Y) := by
        dsimp [Y, b0]
        calc
          |(b : Real) / ((10 ^ length : Nat) : Real) - x| +
                |(s.min' hs : Real) / ((10 ^ length : Nat) : Real) - x| <=
              E / ((10 ^ length : Nat) : Real) +
                E / ((10 ^ length : Nat) : Real) :=
            add_le_add hb' hb0'
          _ = 2 * (E / ((10 ^ length : Nat) : Real)) := by ring
      have hdiff :
          |(b : Real) / Y - (b0 : Real) / Y| <= 2 * (E / Y) := by
        calc
          |(b : Real) / Y - (b0 : Real) / Y| =
              |((b : Real) / Y - x) - ((b0 : Real) / Y - x)| := by ring_nf
          _ <= |(b : Real) / Y - x| + |(b0 : Real) / Y - x| :=
              by simpa [abs_sub_comm] using
              (abs_sub_le ((b : Real) / Y - x) 0
                ((b0 : Real) / Y - x))
          _ <= 2 * (E / Y) := hsum
      have hscaled := mul_le_mul_of_nonneg_right hdiff (le_of_lt hY)
      have hrewrite :
          Y * |(b : Real) / Y - (b0 : Real) / Y| =
            |(b : Real) - (b0 : Real)| := by
        have hquot : (b : Real) / Y - (b0 : Real) / Y =
            ((b : Real) - (b0 : Real)) / Y := by
          field_simp [hY.ne']
        rw [hquot, abs_div, abs_of_pos hY]
        field_simp
      have hscaled' :
          Y * |(b : Real) / Y - (b0 : Real) / Y| <=
            Y * (2 * (E / Y)) := by
        nlinarith [hscaled]
      rw [hrewrite] at hscaled'
      calc
        |(b : Real) - (b0 : Real)| <= Y * (2 * (E / Y)) := hscaled'
        _ = 2 * E := by field_simp [hY.ne']
    have hoffNonneg (b : Int) (hb : b ∈ s) :
        0 <= b - b0 := sub_nonneg.mpr (hb0 b hb)
    have hoffBound (b : Int) (hb : b ∈ s) :
        (b - b0).toNat <= Nat.ceil (2 * E) := by
      have hcast : ((b - b0 : Int) : Real) <= 2 * E := by
        have := hdiam b hb
        rw [abs_of_nonneg (by exact_mod_cast hoffNonneg b hb)] at this
        exact_mod_cast this
      have hnat : b - b0 <= (Nat.ceil (2 * E) : Int) := by
        have hceil : (2 * E : Real) <= Nat.ceil (2 * E) := Nat.le_ceil _
        exact_mod_cast hcast.trans hceil
      have hnatInt : ((b - b0).toNat : Int) = b - b0 :=
        Int.natCast_toNat_eq_self.mpr (hoffNonneg b hb)
      exact_mod_cast (hnatInt ▸ hnat)
    have hceilBlock : Nat.ceil (2 * E) + 1 <= 4 * N := by
      have hceilReal : (Nat.ceil (2 * E) : Real) < 2 * E + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hfourE : 2 * E + 1 <= 4 * E := by nlinarith
      have hfourW : 4 * E <= 4 * (N : Real) := by
        exact mul_le_mul_of_nonneg_left hW (by norm_num)
      have hreal : (Nat.ceil (2 * E) : Real) + 1 <= 4 * (N : Real) := by
        linarith
      exact_mod_cast hreal
    have hoffRange (b : Int) (hb : b ∈ s) :
        (b - b0).toNat < 4 * N := by
      exact lt_of_le_of_lt (hoffBound b hb)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hceilBlock)
    have hoffInjective : Set.InjOn (fun b : Int => (b - b0).toNat) (↑s : Set Int) := by
      intro b hb c hc heq
      have hdiffEq : b - b0 = c - b0 := by
        have hcastEq : ((b - b0).toNat : Int) = ((c - b0).toNat : Int) := by
          exact_mod_cast heq
        rw [Int.natCast_toNat_eq_self.mpr (hoffNonneg b hb),
          Int.natCast_toNat_eq_self.mpr (hoffNonneg c hc)] at hcastEq
        exact hcastEq
      omega
    have hsumImage :
        (∑ b ∈ s,
          normalizedPaddedDigitFourierMagnitudeAt digit w
            ((b : Real) / W)) =
          ∑ n ∈ offsets,
            normalizedPaddedDigitFourierMagnitudeAt digit w
              (((b0 : Real) + n) / W) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro b hb
        have hnonneg := hoffNonneg b hb
        dsimp [W]
        rw [show (b : Real) = (b0 : Real) + (b - b0 : Int) by push_cast; ring,
          show ((b - b0).toNat : Real) = (b - b0 : Real) by
            exact_mod_cast (Int.natCast_toNat_eq_self.mpr hnonneg)]
        congr 1
        field_simp [show (N : Real) ≠ 0 by positivity]
        push_cast
        ring
      · exact hoffInjective
    have hoffSubset : offsets ⊆ Finset.range (4 * N) := by
      intro n hn
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (hoffRange b hb)
    have hnonnegTail (n : Nat) :
        0 <= normalizedPaddedDigitFourierMagnitudeAt digit w
          (((b0 : Real) + n) / W) :=
      normalizedPaddedDigitFourierMagnitudeAt_nonneg digit w _
    have hsubsetSum := Finset.sum_le_sum_of_subset_of_nonneg hoffSubset
      (fun n _ _ => hnonnegTail n)
    have hfour := sum_range_four_shiftedBlocks_le digit w ((b0 : Real) / W)
    have hsumRange :
        (∑ n ∈ Finset.range (4 * N),
          normalizedPaddedDigitFourierMagnitudeAt digit w
            (((b0 : Real) + n) / W)) <=
          80000 * (W ^ largeSieveAlpha) := by
      calc
        _ = ∑ n ∈ Finset.range (4 * N),
            normalizedPaddedDigitFourierMagnitudeAt digit w
              ((b0 : Real) / W + (n : Real) / W) := by
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          field_simp
        _ <= 80000 * (W ^ largeSieveAlpha) := by
          simpa only [N, W] using hfour
    rw [hsumImage]
    calc
      _ <= ∑ n ∈ Finset.range (4 * N),
          normalizedPaddedDigitFourierMagnitudeAt digit w
            (((b0 : Real) + n) / W) := hsubsetSum
      _ <= 80000 * (W ^ largeSieveAlpha) := hsumRange
      _ <= 8000000 * (E ^ largeSieveAlpha) := by
        have hE0 : 0 <= E := by linarith
        have hpow : W ^ largeSieveAlpha <=
            (100 * E) ^ largeSieveAlpha := by
          apply Real.rpow_le_rpow (by positivity) _ largeSieveAlpha_nonneg
          exact hWUpper.le
        have h100 : (100 : Real) ^ largeSieveAlpha <= 100 := by
          have hα1 : largeSieveAlpha <= 1 := by norm_num [largeSieveAlpha]
          nlinarith [Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 100)
            hα1]
        calc
          80000 * W ^ largeSieveAlpha <=
              80000 * ((100 * E) ^ largeSieveAlpha) := by gcongr
          _ = 80000 * (100 ^ largeSieveAlpha) * E ^ largeSieveAlpha := by
            rw [Real.mul_rpow (by positivity : 0 <= (100 : Real)) hE0]
            ring
          _ <= 8000000 * E ^ largeSieveAlpha := by
            gcongr
            nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ b ∈ s,
      normalizedPaddedDigitFourierMagnitudeAt digit w
        ((b : Real) / ((10 ^ w : Nat) : Real))) <= _
    rw [hempty]
    positivity

end

end PrimesRestrictedDigits
