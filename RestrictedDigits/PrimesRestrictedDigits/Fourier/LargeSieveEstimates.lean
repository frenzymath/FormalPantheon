import PrimesRestrictedDigits.Fourier.GridCircleSpacing
import PrimesRestrictedDigits.Fourier.LargeSieveSampling
import PrimesRestrictedDigits.Fourier.ReducedFractionCarrier

/-!
# Repaired large-sieve estimates for restricted digits

This file proves all three conclusions of `MAYNARD-PRD-PUBLISHED`, Lemma 10.5, pp. 175--178.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- One explicit absolute constant valid in all three large-sieve bounds. -/
def largeSieveConstant : Real := 200000000

/-- The complete fixed-denominator grid estimate. The carrier deliberately
retains the source's duplicated periodic endpoint `a = q`. -/
theorem completeGrid_largeSieveEstimate
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    {delta : Real} (hdelta : 0 <= delta) (beta : Real) :
    (∑ a ∈ Finset.range (q + 1),
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
          ((a : Real) / q + beta)) <=
      largeSieveConstant * (1 + delta * q) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  classical
  let value (a : Nat) := closedWindowMaximum
    (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
      ((a : Real) / q + beta)
  let canonicalValue (a : Fin q) := value a.val
  have hqReal : (1 : Real) <= q := by exact_mod_cast hq
  have hseparated : ∀ a ∈ (Finset.univ : Finset (Fin q)),
      ∀ b ∈ (Finset.univ : Finset (Fin q)), a ≠ b ->
        1 / (q : Real) <=
          dist ((((a.val : Real) / q : Real)) : UnitAddCircle)
            ((((b.val : Real) / q : Real)) : UnitAddCircle) := by
    intro a ha b hb hab
    exact one_div_natCast_le_dist_fin_div hq hab
  have hcanonical :=
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
      (Finset.univ : Finset (Fin q)) digit length
      (fun a : Fin q => (a.val : Real) / q) hqReal hdelta hseparated beta
  have hendpoint : value q = value 0 := by
    have hperiod := closedWindowMaximum_add_period
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length)
      (normalizedPaddedDigitFourierMagnitudeAt_periodic digit length)
      hdelta beta
    have hqNe : (q : Real) ≠ 0 := by exact_mod_cast hq.ne'
    dsimp [value]
    rw [div_self hqNe]
    simp only [Nat.cast_zero, zero_div, zero_add]
    simpa only [add_comm] using hperiod
  have hsourceIdentity :
      (∑ a ∈ Finset.range (q + 1), value a) =
        (∑ a : Fin q, canonicalValue a) + value 0 := by
    rw [Finset.sum_range_succ, hendpoint]
    congr 1
    simpa only [canonicalValue] using
      (Fin.sum_univ_eq_sum_range value q).symm
  have hzeroTerm : value 0 <= ∑ a : Fin q, canonicalValue a := by
    let zero : Fin q := ⟨0, hq⟩
    have hnonneg (a : Fin q) : 0 <= canonicalValue a :=
      closedWindowMaximum_nonneg
        (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length)
        (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length) hdelta _
    have hmember : zero ∈ (Finset.univ : Finset (Fin q)) := Finset.mem_univ zero
    have hsingle := Finset.single_le_sum (fun a _ => hnonneg a) hmember
    simpa [zero, canonicalValue, value] using hsingle
  let target : Real :=
    (1 + delta * (q : Real)) *
      ((q : Real) ^ largeSieveAlpha +
        (q : Real) * (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)))
  have htarget0 : 0 <= target := by
    dsimp [target]
    positivity
  change (∑ a ∈ Finset.range (q + 1), value a) <= _
  rw [hsourceIdentity]
  have hcanonical' :
      (∑ a : Fin q, canonicalValue a) <= largeSieveSamplingConstant * target := by
    calc
      (∑ a : Fin q, canonicalValue a) <=
          largeSieveSamplingConstant * (1 + delta * (q : Real)) *
            ((q : Real) ^ largeSieveAlpha +
              (q : Real) *
                (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
        simpa only [canonicalValue, value] using hcanonical
      _ = largeSieveSamplingConstant * target := by
        dsimp [target]
        ring
  calc
    (∑ a : Fin q, canonicalValue a) + value 0 <=
        2 * ∑ a : Fin q, canonicalValue a := by linarith
    _ <= 2 * (largeSieveSamplingConstant * target) := by gcongr
    _ <= largeSieveConstant * target := by
      unfold largeSieveSamplingConstant largeSieveConstant
      nlinarith
    _ = largeSieveConstant * (1 + delta * q) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
      dsimp [target]
      ring

/-- The estimate over all reduced fractions with denominator at most a real
cutoff `Q`. -/
theorem reducedFractions_largeSieveEstimate
    (digit : Fin 10) (length : Nat) {Q : Real} (hQ : 1 <= Q)
    {delta : Real} (hdelta : 0 <= delta) (beta : Real) :
    (∑ pair ∈ reducedFractionCarrier (Nat.floor Q),
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
          (reducedFractionValue pair + beta)) <=
      largeSieveConstant * (1 + delta * Q ^ 2) *
        (Q ^ (54 / 77 : Real) + Q ^ 2 *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hfloorQ : ((Nat.floor Q : Nat) : Real) <= Q := Nat.floor_le hQ0.le
  have hL : 1 <= Q ^ 2 := by nlinarith
  have hseparated :
      ∀ left ∈ reducedFractionCarrier (Nat.floor Q),
        ∀ right ∈ reducedFractionCarrier (Nat.floor Q), left ≠ right ->
          1 / Q ^ 2 <=
            dist ((reducedFractionValue left : Real) : UnitAddCircle)
              ((reducedFractionValue right : Real) : UnitAddCircle) := by
    intro left hleft right hright hne
    exact one_div_sq_le_dist_reducedFractionValue hQ0.le hleft hright
      hfloorQ hne
  have hsample :=
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
      (reducedFractionCarrier (Nat.floor Q)) digit length reducedFractionValue
      hL hdelta hseparated beta
  have hpower : (Q ^ 2) ^ largeSieveAlpha = Q ^ (54 / 77 : Real) := by
    calc
      (Q ^ 2) ^ largeSieveAlpha =
          Real.rpow (Real.rpow Q (2 : Real)) largeSieveAlpha := by
        exact congrArg (fun x : Real => Real.rpow x largeSieveAlpha)
          (Real.rpow_natCast Q 2).symm
      _ = Real.rpow Q ((2 : Real) * largeSieveAlpha) :=
        (Real.rpow_mul hQ0.le _ _).symm
      _ = Real.rpow Q (54 / 77 : Real) := by
        congr 1
        norm_num [largeSieveAlpha]
  let target : Real := (1 + delta * Q ^ 2) *
    (Q ^ (54 / 77 : Real) + Q ^ 2 *
      (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)))
  have htarget0 : 0 <= target := by
    dsimp [target]
    positivity
  have hsample' :
      (∑ pair ∈ reducedFractionCarrier (Nat.floor Q),
        closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
            (reducedFractionValue pair + beta)) <=
        largeSieveSamplingConstant * target := by
    calc
      _ <= largeSieveSamplingConstant * (1 + delta * Q ^ 2) *
          ((Q ^ 2) ^ largeSieveAlpha + Q ^ 2 *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := hsample
      _ = largeSieveSamplingConstant * target := by
        dsimp [target]
        rw [hpower]
        ring
  calc
    _ <= largeSieveSamplingConstant * target := hsample'
    _ <= largeSieveConstant * target := by
      unfold largeSieveSamplingConstant largeSieveConstant
      nlinarith
    _ = _ := by
      dsimp [target]
      ring

/-- The reduced-fraction estimate when every denominator is divisible by the
positive natural `d`. -/
theorem divisibleReducedFractions_largeSieveEstimate
    (digit : Fin 10) (length d : Nat) (hd : 0 < d)
    {Q : Real} (hQ : 1 <= Q) {delta : Real} (hdelta : 0 <= delta)
    (beta : Real) :
    (∑ pair ∈ divisibleReducedFractionCarrier (Nat.floor Q) d,
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
          (reducedFractionValue pair + beta)) <=
      largeSieveConstant * (1 + delta * (Q ^ 2 / d)) *
        ((Q ^ 2 / d) ^ largeSieveAlpha + (Q ^ 2 / d) *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  let carrier := divisibleReducedFractionCarrier (Nat.floor Q) d
  let L : Real := Q ^ 2 / d
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hdReal : 0 < (d : Real) := by exact_mod_cast hd
  have hL0 : 0 < L := by
    dsimp [L]
    positivity
  rcases carrier.eq_empty_or_nonempty with hempty | hnonempty
  · change (∑ pair ∈ carrier, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        (reducedFractionValue pair + beta)) <= _
    rw [hempty]
    simp only [Finset.sum_empty]
    have hright0 : 0 <= largeSieveConstant * (1 + delta * L) *
        (L ^ largeSieveAlpha + L *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
      unfold largeSieveConstant
      positivity
    simpa only [L] using hright0
  · obtain ⟨pair, hpair⟩ := hnonempty
    have hpair' := mem_divisibleReducedFractionCarrier_iff.mp hpair
    have hqPos : 0 < pair.1 :=
      lt_of_lt_of_le Nat.zero_lt_one
        (mem_reducedFractionCarrier_iff.mp hpair'.1).1
    have hdq : d <= pair.1 := Nat.le_of_dvd hqPos hpair'.2
    have hqFloor : pair.1 <= Nat.floor Q :=
      (mem_reducedFractionCarrier_iff.mp hpair'.1).2.1
    have hfloorQ : ((Nat.floor Q : Nat) : Real) <= Q := Nat.floor_le hQ0.le
    have hdQ : (d : Real) <= Q := by
      exact (by exact_mod_cast hdq : (d : Real) <= pair.1).trans
        ((by exact_mod_cast hqFloor : (pair.1 : Real) <= Nat.floor Q).trans hfloorQ)
    have hL : 1 <= L := by
      dsimp [L]
      apply (le_div_iff₀ hdReal).mpr
      calc
        (1 : Real) * d = (d : Real) := by ring
        _ <= Q := hdQ
        _ <= Q * Q := by nlinarith
        _ = Q ^ 2 := by ring
    have hseparated : ∀ left ∈ carrier, ∀ right ∈ carrier, left ≠ right ->
        1 / L <=
          dist ((reducedFractionValue left : Real) : UnitAddCircle)
            ((reducedFractionValue right : Real) : UnitAddCircle) := by
      intro left hleft right hright hne
      have hspacing := natCast_div_sq_le_dist_divisibleReducedFractionValue
        hd hQ0 hleft hright (Nat.floor_le hQ0.le) hne
      have hreciprocal : 1 / L = (d : Real) / Q ^ 2 := by
        dsimp [L]
        field_simp
      rw [hreciprocal]
      exact hspacing
    have hsample :=
      sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
        carrier digit length reducedFractionValue hL hdelta hseparated beta
    let target : Real := (1 + delta * L) *
      (L ^ largeSieveAlpha + L *
        (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)))
    have htarget0 : 0 <= target := by
      dsimp [target]
      positivity
    have hsample' :
        (∑ pair ∈ carrier, closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
            (reducedFractionValue pair + beta)) <=
          largeSieveSamplingConstant * target := by
      calc
        _ <= largeSieveSamplingConstant * (1 + delta * L) *
            (L ^ largeSieveAlpha + L *
              (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := hsample
        _ = largeSieveSamplingConstant * target := by
          dsimp [target]
          ring
    change (∑ pair ∈ carrier, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        (reducedFractionValue pair + beta)) <= _
    calc
      _ <= largeSieveSamplingConstant * target := hsample'
      _ <= largeSieveConstant * target := by
        unfold largeSieveSamplingConstant largeSieveConstant
        nlinarith
      _ = _ := by
        dsimp [target, L]
        ring

end

end PrimesRestrictedDigits
