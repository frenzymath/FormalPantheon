import PrimesRestrictedDigits.MajorArcs.M1Decay
import PrimesRestrictedDigits.MajorArcs.M1Weight
import PrimesRestrictedDigits.MajorArcs.PartitionCardinalityLogScale

/-!
# Contribution of the repaired first major-arc class

This formalizes the finite aggregation and logarithmic absorption in
`MAYNARD-PRD-PUBLISHED`, p. 186, Eq. (11.1), for one fixed region arity.
-/

open scoped BigOperators
open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- The normalized contribution of the repaired first-class frequency
carrier. -/
noncomputable def majorArcClassOneContribution
    (X : Nat) (Q : Real) (A s : Finset Nat)
    (w : Nat → Complex) : Complex :=
  (∑ h ∈ majorArcClassOneFrequencies X Q,
      majorArcWeightedPhaseSum A (fun _ => 1)
          ((h : Real) / (X : Real)) *
        majorArcWeightedPhaseSum s w (-((h : Real) / (X : Real)))) /
    (X : Complex)

/-- Pointwise bounds for both transforms aggregate over the finite repaired
first class. -/
theorem norm_majorArcClassOneContribution_le
    {X : Nat} (hX : 0 < X) (Q : Real)
    (A s : Finset Nat) (w : Nat → Complex)
    {digitBound regionBound : Real}
    (hdigitBound : 0 ≤ digitBound) (hregionBound : 0 ≤ regionBound)
    (hdigit : ∀ h ∈ majorArcClassOneFrequencies X Q,
      ‖majorArcWeightedPhaseSum A (fun _ => 1)
          ((h : Real) / (X : Real))‖ ≤ digitBound)
    (hregion : ∀ h ∈ majorArcClassOneFrequencies X Q,
      ‖majorArcWeightedPhaseSum s w
          (-((h : Real) / (X : Real)))‖ ≤ regionBound) :
    ‖majorArcClassOneContribution X Q A s w‖ ≤
      ((majorArcClassOneFrequencies X Q).card : Real) *
        digitBound * regionBound / (X : Real) := by
  let F := majorArcClassOneFrequencies X Q
  let term : Nat → Complex := fun h =>
    majorArcWeightedPhaseSum A (fun _ => 1)
        ((h : Real) / (X : Real)) *
      majorArcWeightedPhaseSum s w (-((h : Real) / (X : Real)))
  have hsum : ‖∑ h ∈ F, term h‖ ≤
      (F.card : Real) * digitBound * regionBound := by
    calc
      ‖∑ h ∈ F, term h‖ ≤ ∑ h ∈ F, ‖term h‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ F, digitBound * regionBound := by
        gcongr with h hh
        dsimp [term]
        rw [norm_mul]
        calc
          ‖majorArcWeightedPhaseSum A (fun _ => 1)
                ((h : Real) / (X : Real))‖ *
              ‖majorArcWeightedPhaseSum s w
                (-((h : Real) / (X : Real)))‖ ≤
              digitBound *
                ‖majorArcWeightedPhaseSum s w
                  (-((h : Real) / (X : Real)))‖ :=
            mul_le_mul_of_nonneg_right (hdigit h hh) (norm_nonneg _)
          _ ≤ digitBound * regionBound :=
            mul_le_mul_of_nonneg_left (hregion h hh) hdigitBound
      _ = (F.card : Real) * digitBound * regionBound := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have _hupperNonneg : 0 ≤ digitBound * regionBound :=
    mul_nonneg hdigitBound hregionBound
  change ‖(∑ h ∈ F, term h) / (X : Complex)‖ ≤ _
  rw [norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right hsum (by positivity)

private theorem majorArcPhase_padded_grid (K frequency n : Nat) :
    majorArcPhase
        ((n : Real) * ((frequency : Real) / (((10 ^ K : Nat) : Real)))) =
      digitPhase K frequency n := by
  rw [majorArcPhase, digitPhase]
  congr 1
  push_cast
  ring

/-- The positive padded decimal phase sum is the digit Fourier transform. -/
theorem majorArcWeightedPhaseSum_padded_eq
    (digit : Fin 10) (K frequency : Nat) :
    majorArcWeightedPhaseSum (paddedRestrictedNumbers digit K)
        (fun _ => 1)
        ((frequency : Real) / (((10 ^ K : Nat) : Real))) =
      paddedDigitFourierSum digit K frequency := by
  unfold majorArcWeightedPhaseSum paddedDigitFourierSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [one_mul, majorArcPhase_padded_grid]

/-- The unit-weight digit phase norm is exactly its padded cardinality times
the normalized grid magnitude. -/
theorem norm_majorArcPaddedDigitPhaseSum_eq
    (digit : Fin 10) (K frequency : Nat) :
    ‖majorArcWeightedPhaseSum (paddedRestrictedNumbers digit K)
        (fun _ => 1)
        ((frequency : Real) / (((10 ^ K : Nat) : Real)))‖ =
      ((paddedRestrictedNumbers digit K).card : Real) *
        normalizedPaddedDigitFourierMagnitude digit K frequency := by
  rw [majorArcWeightedPhaseSum_padded_eq,
    normalizedPaddedDigitFourierMagnitude, card_paddedRestrictedNumbers]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The finite M1 aggregate after inserting a normalized digit bound and the
explicit trivial region transform bound. -/
theorem norm_majorArcClassOneRegionContribution_le
    (digit : Fin 10) {X K : Nat} (hpower : X = 10 ^ K)
    (hX : 3 ≤ X) {Q E : Real} (hE : 0 ≤ E)
    (hdecay : ∀ frequency ∈ majorArcClassOneFrequencies X Q,
      normalizedPaddedDigitFourierMagnitude digit K frequency ≤ E)
    {r : Nat} (a : Fin r → Real) (delta regionEta : Real) :
    ‖majorArcClassOneContribution X Q
        (paddedRestrictedNumbers digit K) (Finset.range X)
        (fun n =>
          (majorArcRegionWeightAtProduct X a delta regionEta n : Complex))‖ ≤
      ((majorArcClassOneFrequencies X Q).card : Real) *
        ((paddedRestrictedNumbers digit K).card : Real) * E *
          (2 * Real.log 4 * Real.log (X : Real)) ^ (r + 1) := by
  subst X
  let X : Nat := 10 ^ K
  let A := paddedRestrictedNumbers digit K
  let W : Nat → Complex := fun n =>
    (majorArcRegionWeightAtProduct X a delta regionEta n : Complex)
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hdigitNonneg :
      0 ≤ (A.card : Real) * E := mul_nonneg (by positivity) hE
  have hregionNonneg :
      0 ≤ (X : Real) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ (r + 1) := by
    have hlog : 0 ≤ Real.log (X : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    positivity
  have haggregate := norm_majorArcClassOneContribution_le
    hXpos Q A (Finset.range X) W hdigitNonneg hregionNonneg
    (fun h hh => by
      change
        ‖majorArcWeightedPhaseSum (paddedRestrictedNumbers digit K)
            (fun _ => 1)
            ((h : Real) / (((10 ^ K : Nat) : Real)))‖ ≤
          (A.card : Real) * E
      rw [norm_majorArcPaddedDigitPhaseSum_eq]
      gcongr
      exact hdecay h (by simpa only [X] using hh))
    (fun h hh =>
      norm_majorArcRegionWeightedPhaseSum_le_log_pow X a delta regionEta
        (-((h : Real) / (X : Real))) (by simpa only [X] using hX))
  have hXreal : (X : Real) ≠ 0 := by positivity
  change ‖majorArcClassOneContribution X Q A (Finset.range X) W‖ ≤ _
  calc
    ‖majorArcClassOneContribution X Q A (Finset.range X) W‖ ≤
        ((majorArcClassOneFrequencies X Q).card : Real) *
          ((A.card : Real) * E) *
          ((X : Real) *
            (2 * Real.log 4 * Real.log (X : Real)) ^ (r + 1)) /
          (X : Real) := haggregate
    _ = ((majorArcClassOneFrequencies X Q).card : Real) *
        (A.card : Real) * E *
          (2 * Real.log 4 * Real.log (X : Real)) ^ (r + 1) := by
      field_simp

private theorem tendsto_sqrt_log_ten_pow :
    Tendsto
      (fun K : Nat => Real.sqrt
        (Real.log (((10 ^ K : Nat) : Real)))) atTop atTop := by
  have hlinear :
      Tendsto (fun K : Nat => (K : Real) * Real.log 10) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const
      (Real.log_pos (by norm_num : (1 : Real) < 10))
  convert Real.tendsto_sqrt_atTop.comp hlinear using 1
  funext K
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

/-- The square-root-logarithmic decay absorbs the repaired class count, the
region log powers, and the requested denominator. -/
theorem exists_majorArcClassOneContributionAbsorptionThreshold
    (D r : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K →
      70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) ≤
        1 / Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  let N : Nat := 4 * D + (r + 1)
  let B : Real := 70 * (2 * Real.log 4) ^ (r + 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hlittleO :
      (fun y : Real => B * y ^ (2 * N)) =o[atTop] Real.exp :=
    (Real.isLittleO_pow_exp_atTop (n := 2 * N)).const_mul_left B
  have hbound : ∀ᶠ y : Real in atTop,
      ‖B * y ^ (2 * N)‖ ≤ 1 * ‖Real.exp y‖ :=
    hlittleO.bound zero_lt_one
  have hpulled : ∀ᶠ K : Nat in atTop,
      (1 ≤ K) ∧
      ‖B * (Real.sqrt (Real.log (((10 ^ K : Nat) : Real)))) ^ (2 * N)‖ ≤
        1 * ‖Real.exp
          (Real.sqrt (Real.log (((10 ^ K : Nat) : Real))))‖ :=
    (eventually_ge_atTop (1 : Nat)).and
      (tendsto_sqrt_log_ten_pow.eventually hbound)
  rcases eventually_atTop.mp hpulled with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hdata := hK0 K hK
  let L : Real := Real.log (((10 ^ K : Nat) : Real))
  let y : Real := Real.sqrt L
  have hLidentity : L = (K : Real) * Real.log 10 := by
    dsimp [L]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hL : 0 < L := by
    rw [hLidentity]
    exact mul_pos (by exact_mod_cast hdata.1)
      (Real.log_pos (by norm_num))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hySq : y ^ 2 = L := Real.sq_sqrt hL.le
  have hpoly : B * y ^ (2 * N) ≤ Real.exp y := by
    have hnorm := hdata.2
    change ‖B * y ^ (2 * N)‖ ≤ 1 * ‖Real.exp y‖ at hnorm
    rw [Real.norm_of_nonneg (mul_nonneg hB (pow_nonneg hy _)),
      Real.norm_of_nonneg (Real.exp_pos y).le, one_mul] at hnorm
    exact hnorm
  have hcore : B * L ^ N * Real.exp (-y) ≤ 1 := by
    have hpower : y ^ (2 * N) = L ^ N := by
      rw [pow_mul, hySq]
    rw [← hpower]
    calc
      B * y ^ (2 * N) * Real.exp (-y) ≤
          Real.exp y * Real.exp (-y) := by
        gcongr
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have hLD : 0 < L ^ D := pow_pos hL D
  change
    70 * L ^ (3 * D) * Real.exp (-y) *
        (2 * Real.log 4 * L) ^ (r + 1) ≤ 1 / L ^ D
  rw [le_div_iff₀ hLD]
  calc
    (70 * L ^ (3 * D) * Real.exp (-y) *
        (2 * Real.log 4 * L) ^ (r + 1)) * L ^ D =
        B * L ^ N * Real.exp (-y) := by
      dsimp [B, N]
      rw [mul_pow]
      ring
    _ ≤ 1 := hcore

private theorem self_le_ten_pow (K : Nat) : K ≤ 10 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ]
      have hpow : 0 < 10 ^ K := by positivity
      omega

private theorem exists_majorArcClassOneBoundedArityAbsorptionThreshold
    (D R : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ r : Nat, r ≤ R →
      70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) ≤
        1 / Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  rcases exists_majorArcClassOneContributionAbsorptionThreshold D R with
    ⟨K1, hK1⟩
  refine ⟨max K1 1, ?_⟩
  intro K hK r hr
  have hKK1 : K1 ≤ K := (le_max_left K1 1).trans hK
  have hKpos : 1 ≤ K := (le_max_right K1 1).trans hK
  let L : Real := Real.log (((10 ^ K : Nat) : Real))
  have hLidentity : L = (K : Real) * Real.log 10 := by
    dsimp [L]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogTenOne : (1 : Real) < Real.log 10 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2
      (Real.exp_one_lt_three.trans_le (by norm_num))
  have hLone : (1 : Real) ≤ L := by
    have hKreal : (1 : Real) ≤ K := by exact_mod_cast hKpos
    have hlogTenLe : Real.log 10 ≤ (K : Real) * Real.log 10 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hKreal
          (Real.log_pos (by norm_num)).le
    rw [hLidentity]
    exact hlogTenOne.le.trans hlogTenLe
  have hlogFourOne : (1 : Real) < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2
      (Real.exp_one_lt_three.trans_le (by norm_num))
  have hconstant : (1 : Real) ≤ 2 * Real.log 4 := by linarith
  have hbase : (1 : Real) ≤ 2 * Real.log 4 * L := by
    simpa only [one_mul] using
      mul_le_mul hconstant hLone zero_le_one (by positivity)
  have hpow : (2 * Real.log 4 * L) ^ (r + 1) ≤
      (2 * Real.log 4 * L) ^ (R + 1) :=
    pow_le_pow_right₀ hbase (by omega)
  change
    70 * L ^ (3 * D) * Real.exp (-Real.sqrt L) *
        (2 * Real.log 4 * L) ^ (r + 1) ≤ 1 / L ^ D
  calc
    70 * L ^ (3 * D) * Real.exp (-Real.sqrt L) *
        (2 * Real.log 4 * L) ^ (r + 1) ≤
      70 * L ^ (3 * D) * Real.exp (-Real.sqrt L) *
        (2 * Real.log 4 * L) ^ (R + 1) := by
      gcongr
    _ ≤ 1 / L ^ D := by
      simpa only [L] using hK1 K hKK1

/-- The complete repaired first-class contribution has the source logarithmic
saving for every fixed region arity. -/
theorem exists_majorArcClassOneRegionContributionThreshold
    (D r : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ digit : Fin 10,
      ∀ a : Fin r → Real, ∀ delta regionEta : Real,
      ‖majorArcClassOneContribution (10 ^ K)
          (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n =>
            (majorArcRegionWeightAtProduct (10 ^ K) a delta regionEta n :
              Complex))‖ ≤
        ((paddedRestrictedNumbers digit K).card : Real) /
          Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  rcases exists_majorArcClassOnePointwiseDecayThreshold D with
    ⟨KDecay, hdecay⟩
  rcases exists_majorArcLogPowerThreshold D with ⟨XScale, hscale⟩
  rcases exists_majorArcClassOneContributionAbsorptionThreshold D r with
    ⟨KAbsorb, habsorb⟩
  refine ⟨max KDecay (max KAbsorb XScale), ?_⟩
  intro K hK digit a delta regionEta
  have hKDecay : KDecay ≤ K :=
    (le_max_left KDecay (max KAbsorb XScale)).trans hK
  have hKAbsorb : KAbsorb ≤ K :=
    (le_max_of_le_right (le_max_left KAbsorb XScale)).trans hK
  have hXScaleK : XScale ≤ K :=
    (le_max_of_le_right (le_max_right KAbsorb XScale)).trans hK
  have hscaleK := hscale (10 ^ K) (hXScaleK.trans (self_le_ten_pow K))
  have haggregate := norm_majorArcClassOneRegionContribution_le
    digit (X := 10 ^ K) (K := K) rfl (by omega)
    (E := Real.exp (-Real.sqrt
      (Real.log (((10 ^ K : Nat) : Real))))) (by positivity)
    (fun frequency hfrequency =>
      hdecay K hKDecay digit frequency hfrequency)
    a delta regionEta
  have hcard := majorArcClassOneFrequencies_card_log_pow_le
    hscaleK.1 hscaleK.2
  calc
    ‖majorArcClassOneContribution (10 ^ K)
        (Real.log (((10 ^ K : Nat) : Real)) ^ D)
        (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
        (fun n =>
          (majorArcRegionWeightAtProduct (10 ^ K) a delta regionEta n :
            Complex))‖ ≤
        ((majorArcClassOneFrequencies (10 ^ K)
          (Real.log (((10 ^ K : Nat) : Real)) ^ D)).card : Real) *
          ((paddedRestrictedNumbers digit K).card : Real) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) := haggregate
    _ ≤ (70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D)) *
          ((paddedRestrictedNumbers digit K).card : Real) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) := by
      gcongr
    _ = ((paddedRestrictedNumbers digit K).card : Real) *
        (70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1)) := by ring
    _ ≤ ((paddedRestrictedNumbers digit K).card : Real) *
        (1 / Real.log (((10 ^ K : Nat) : Real)) ^ D) :=
      mul_le_mul_of_nonneg_left (habsorb K hKAbsorb) (by positivity)
    _ = ((paddedRestrictedNumbers digit K).card : Real) /
        Real.log (((10 ^ K : Nat) : Real)) ^ D := by ring

/-- One threshold gives the source logarithmic saving for every prefix arity
bounded before the threshold is chosen. -/
theorem exists_majorArcClassOneBoundedArityRegionContributionThreshold
    (D R : Nat) :
    ∃ K0 : Nat, ∀ K : Nat, K0 ≤ K → ∀ r : Nat, r ≤ R →
      ∀ digit : Fin 10, ∀ a : Fin r → Real, ∀ delta regionEta : Real,
      ‖majorArcClassOneContribution (10 ^ K)
          (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n =>
            (majorArcRegionWeightAtProduct (10 ^ K) a delta regionEta n :
              Complex))‖ ≤
        ((paddedRestrictedNumbers digit K).card : Real) /
          Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  rcases exists_majorArcClassOnePointwiseDecayThreshold D with
    ⟨KDecay, hdecay⟩
  rcases exists_majorArcLogPowerThreshold D with ⟨XScale, hscale⟩
  rcases exists_majorArcClassOneBoundedArityAbsorptionThreshold D R with
    ⟨KAbsorb, habsorb⟩
  refine ⟨max KDecay (max KAbsorb XScale), ?_⟩
  intro K hK r hr digit a delta regionEta
  have hKDecay : KDecay ≤ K :=
    (le_max_left KDecay (max KAbsorb XScale)).trans hK
  have hKAbsorb : KAbsorb ≤ K :=
    (le_max_of_le_right (le_max_left KAbsorb XScale)).trans hK
  have hXScaleK : XScale ≤ K :=
    (le_max_of_le_right (le_max_right KAbsorb XScale)).trans hK
  have hscaleK := hscale (10 ^ K) (hXScaleK.trans (self_le_ten_pow K))
  have haggregate := norm_majorArcClassOneRegionContribution_le
    digit (X := 10 ^ K) (K := K) rfl (by omega)
    (E := Real.exp (-Real.sqrt
      (Real.log (((10 ^ K : Nat) : Real))))) (by positivity)
    (fun frequency hfrequency =>
      hdecay K hKDecay digit frequency hfrequency)
    a delta regionEta
  have hcard := majorArcClassOneFrequencies_card_log_pow_le
    hscaleK.1 hscaleK.2
  calc
    ‖majorArcClassOneContribution (10 ^ K)
        (Real.log (((10 ^ K : Nat) : Real)) ^ D)
        (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
        (fun n =>
          (majorArcRegionWeightAtProduct (10 ^ K) a delta regionEta n :
            Complex))‖ ≤
        ((majorArcClassOneFrequencies (10 ^ K)
          (Real.log (((10 ^ K : Nat) : Real)) ^ D)).card : Real) *
          ((paddedRestrictedNumbers digit K).card : Real) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) := haggregate
    _ ≤ (70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D)) *
          ((paddedRestrictedNumbers digit K).card : Real) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1) := by
      gcongr
    _ = ((paddedRestrictedNumbers digit K).card : Real) *
        (70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D) *
          Real.exp (-Real.sqrt
            (Real.log (((10 ^ K : Nat) : Real)))) *
          (2 * Real.log 4 * Real.log (((10 ^ K : Nat) : Real))) ^
            (r + 1)) := by ring
    _ ≤ ((paddedRestrictedNumbers digit K).card : Real) *
        (1 / Real.log (((10 ^ K : Nat) : Real)) ^ D) :=
      mul_le_mul_of_nonneg_left
        (habsorb K hKAbsorb r hr) (by positivity)
    _ = ((paddedRestrictedNumbers digit K).card : Real) /
        Real.log (((10 ^ K : Nat) : Real)) ^ D := by ring

end PrimesRestrictedDigits
