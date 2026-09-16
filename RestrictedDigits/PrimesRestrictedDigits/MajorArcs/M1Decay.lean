import PrimesRestrictedDigits.Fourier.LInfBound
import PrimesRestrictedDigits.MajorArcs.LInfSideConditions

/-!
# Pointwise decay on the repaired first major-arc class

This specializes the repaired Lemma 10.1 to the canonical first-class
frequencies in `MAYNARD-PRD-PUBLISHED`, Section 11, p. 186.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

private theorem eventually_natCast_mul_log_le_sqrt_div (D : Nat) :
    ∀ᶠ L : Real in atTop,
      (D : Real) * Real.log L ≤ Real.sqrt L / 200000000 ∧ 4 ≤ L := by
  have hbound :=
    ((isLittleO_log_rpow_atTop
      (r := (1 / 2 : Real)) (by norm_num)).const_mul_left (D : Real)).bound
        (by norm_num : (0 : Real) < 1 / 200000000)
  filter_upwards [hbound, eventually_ge_atTop (4 : Real)] with L hLbound hL
  refine ⟨?_, hL⟩
  have hL0 : 0 ≤ L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hleft : 0 ≤ (D : Real) * Real.log L :=
    mul_nonneg (by positivity) hlog
  have hright : 0 ≤ L ^ (1 / 2 : Real) :=
    Real.rpow_nonneg hL0 _
  rw [Real.norm_eq_abs, abs_of_nonneg hleft,
    Real.norm_eq_abs, abs_of_nonneg hright] at hLbound
  rw [Real.sqrt_eq_rpow]
  nlinarith

private theorem sourceDecay_le_sqrtDecay_of_logBound
    {D q : Nat} {L : Real}
    (hL : 4 ≤ L)
    (hsmall :
      (D : Real) * Real.log L ≤ Real.sqrt L / 200000000)
    (hq : 2 ≤ q) (hqL : (q : Real) ≤ L ^ D) :
    3 * Real.exp (-(1 / 100000000 : Real) *
        (L / Real.log (q : Real))) ≤
      Real.exp (-Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith
  have hqOne : 1 < q := lt_of_lt_of_le (by omega : 1 < 2) hq
  have hqRealPos : (0 : Real) < q := by positivity
  have hlogqPos : 0 < Real.log (q : Real) :=
    Real.log_pos (by exact_mod_cast hqOne)
  have hlogq : Real.log (q : Real) ≤ (D : Real) * Real.log L := by
    calc
      Real.log (q : Real) ≤ Real.log (L ^ D) :=
        Real.log_le_log hqRealPos hqL
      _ = (D : Real) * Real.log L := Real.log_pow L D
  have hlogqSmall :
      Real.log (q : Real) ≤ Real.sqrt L / 200000000 :=
    hlogq.trans hsmall
  have hsqrtNonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsqrtTwo : (2 : Real) ≤ Real.sqrt L := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hratio :
      200000000 * Real.sqrt L ≤ L / Real.log (q : Real) := by
    rw [le_div_iff₀ hlogqPos]
    calc
      200000000 * Real.sqrt L * Real.log (q : Real) ≤
          200000000 * Real.sqrt L *
            (Real.sqrt L / 200000000) := by
        gcongr
      _ = Real.sqrt L ^ 2 := by ring
      _ = L := Real.sq_sqrt hL0
  have hexponent :
      -(1 / 100000000 : Real) *
          (L / Real.log (q : Real)) ≤
        -2 * Real.sqrt L := by
    nlinarith
  have hthree : (3 : Real) ≤ Real.exp (Real.sqrt L) := by
    calc
      (3 : Real) ≤ Real.sqrt L + 1 := by linarith
      _ ≤ Real.exp (Real.sqrt L) := Real.add_one_le_exp _
  calc
    3 * Real.exp (-(1 / 100000000 : Real) *
        (L / Real.log (q : Real))) ≤
        3 * Real.exp (-2 * Real.sqrt L) := by
      gcongr
    _ ≤ Real.exp (Real.sqrt L) *
        Real.exp (-2 * Real.sqrt L) := by
      gcongr
    _ = Real.exp (-Real.sqrt L) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The explicit Lemma 10.1 decay is eventually stronger than the
square-root-logarithmic decay used in Section 11. -/
theorem exists_sourceDecay_le_sqrtLogPowerThreshold (D : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ q : Nat, 2 ≤ q →
      (q : Real) ≤ Real.log (((10 ^ K : Nat) : Real)) ^ D →
      3 * Real.exp (-(1 / 100000000 : Real) *
          (Real.log (((10 ^ K : Nat) : Real)) /
            Real.log (q : Real))) ≤
        Real.exp (-Real.sqrt
          (Real.log (((10 ^ K : Nat) : Real)))) := by
  have hlogTendsto :
      Tendsto (fun K : Nat => Real.log (((10 ^ K : Nat) : Real)))
        atTop atTop := by
    have hlinear :
        Tendsto (fun K : Nat => (K : Real) * Real.log 10) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := Real)).atTop_mul_const
        (Real.log_pos (by norm_num))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hlinear
  have heventual :=
    hlogTendsto.eventually (eventually_natCast_mul_log_le_sqrt_div D)
  rcases eventually_atTop.mp heventual with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK q hq hqBound
  rcases hK0 K hK with ⟨hsmall, hlogFour⟩
  exact sourceDecay_le_sqrtDecay_of_logBound hlogFour hsmall hq hqBound

/-- The canonical rational plus its signed approximation error is exactly the
grid frequency. -/
theorem majorArcCanonicalPhase_identity
    (X frequency : Nat) (r : Rat) :
    (r.num : Real) / (r.den : Real) +
        ((frequency : Real) / (X : Real) - (r : Real)) =
      (frequency : Real) / (X : Real) := by
  rw [Rat.cast_def]
  ring

/-- The canonical continuous phase is the existing padded decimal grid
transform. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_majorArcCanonicalPhase
    (digit : Fin 10) (K frequency : Nat) (r : Rat) :
    normalizedPaddedDigitFourierMagnitudeAt digit K
        ((r.num : Real) / (r.den : Real) +
          ((frequency : Real) / (((10 ^ K : Nat) : Real)) -
            (r : Real))) =
      normalizedPaddedDigitFourierMagnitude digit K frequency := by
  rw [majorArcCanonicalPhase_identity]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    normalizedPaddedDigitFourierMagnitudeAt_grid digit K frequency

/-- Every repaired first-class frequency has square-root-logarithmic padded
digit decay beyond a threshold depending only on the log exponent. -/
theorem exists_majorArcClassOnePaddedDigitDecayThreshold (D : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ digit : Fin 10,
      ∀ frequency : Nat,
        majorArcClassOne (10 ^ K) frequency
            (Real.log (((10 ^ K : Nat) : Real)) ^ D) →
          normalizedPaddedDigitFourierMagnitude digit K frequency ≤
            Real.exp (-Real.sqrt
              (Real.log (((10 ^ K : Nat) : Real)))) := by
  rcases exists_majorArcClassOneLInfSourceHypothesesThreshold D with
    ⟨K1, hK1⟩
  rcases exists_sourceDecay_le_sqrtLogPowerThreshold D with ⟨K2, hK2⟩
  refine ⟨max K1 K2, ?_⟩
  intro K hK digit frequency hclass
  have hKOne : K1 ≤ K := (le_max_left K1 K2).trans hK
  have hKDecay : K2 ≤ K := (le_max_right K1 K2).trans hK
  rcases hK1 K hKOne frequency hclass with
    ⟨r, q1, q2, hr, hden, _, hq1Coprime, hq1,
      hreduced, hdenSmall, herrorSmall⟩
  have hproductPos : 0 < q1 * q2 := by
    rw [← hden]
    exact r.den_pos
  have hq2 : 0 < q2 := Nat.pos_of_mul_pos_left hproductPos
  have hqTwo : 2 ≤ r.den := by
    calc
      2 ≤ q1 := hq1
      _ ≤ q1 * q2 := Nat.le_mul_of_pos_right q1 hq2
      _ = r.den := hden.symm
  have hsource :=
    normalizedPaddedDigitFourierMagnitudeAt_le_sourceDecay digit
      hden hq2 hq1 hq1Coprime hreduced hdenSmall herrorSmall
  rw [normalizedPaddedDigitFourierMagnitudeAt_majorArcCanonicalPhase]
    at hsource
  exact hsource.trans (hK2 K hKDecay r.den hqTwo hr.2)

/-- Source-facing finset form of the repaired first-class pointwise decay. -/
theorem exists_majorArcClassOnePointwiseDecayThreshold (D : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ digit : Fin 10,
      ∀ frequency : Nat,
        frequency ∈ majorArcClassOneFrequencies (10 ^ K)
            (Real.log (((10 ^ K : Nat) : Real)) ^ D) →
          normalizedPaddedDigitFourierMagnitude digit K frequency ≤
            Real.exp (-Real.sqrt
              (Real.log (((10 ^ K : Nat) : Real)))) := by
  rcases exists_majorArcClassOnePaddedDigitDecayThreshold D with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK digit frequency hfrequency
  classical
  rw [majorArcClassOneFrequencies, Finset.mem_filter] at hfrequency
  exact hK0 K hK digit frequency hfrequency.2

end PrimesRestrictedDigits
