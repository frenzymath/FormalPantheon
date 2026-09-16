import PrimesRestrictedDigits.MajorArcs.M2Absorption
import PrimesRestrictedDigits.MajorArcs.PartitionCardinalityLogScale
import PrimesRestrictedDigits.Digits.Cardinality

/-!
# The repaired M2 contribution at the source logarithmic scale

This specializes the conditional estimate to Maynard's choices `delta = (log (log X))⁻¹` and
`Q = (log X)^D`, then aggregates the repaired second major-arc class. The progression estimate
remains an explicit input.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/--
The exact estimate implies the source-scale pointwise bound for one fixed signed rational
phase.
-/
theorem norm_majorArcRegionWeightedPhaseSum_logScale_le
    {X K D k q : Nat} {a : Fin k -> Real} {eta E : Real} {b c : Int}
    (hX : 4 <= X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) <= 2 / eta)
    (hloglog : Real.exp (Real.exp (12 / eta ^ 2)) <= (X : Real))
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (_hqlog : (q : Real) <= Real.log (X : Real) ^ D)
    (hE : 0 <= E) (hc0 : c ≠ 0)
    (hc : |(c : Real)| <= Real.log (X : Real) ^ D)
    (hscale : majorArcM2LogScaleCoefficient X D k eta E c <=
      3 * (X : Real) / Real.log (X : Real) ^ (4 * D))
    (herror : ∀ m ∈ Finset.Ico 1 X,
      projectedPrimeBoxWeightAtProduct X a (majorArcM2LogLogDelta X) m ≠ 0 ->
      ∀ j ∈ Finset.Ico 1 (majorArcLogSubdivisionCount X D (k + 1)),
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum (X : Real)
            (majorArcLogSubdivisionCount X D (k + 1)) m j q r -
            majorArcPositiveBlockMainTerm (X : Real)
              (majorArcLogSubdivisionCount X D (k + 1)) m q| <=
          E * majorArcPositiveBlockErrorScale (X : Real)
            (majorArcLogSubdivisionCount X D (k + 1)) m q) :
    ‖majorArcWeightedPhaseSum (Finset.range X)
      (fun n => (majorArcRegionWeightAtProduct X a
        (majorArcM2LogLogDelta X) eta n : Complex))
      ((b : Real) / (q : Real) + (c : Real) / (X : Real))‖ <=
        3 * (X : Real) / Real.log (X : Real) ^ (4 * D) := by
  have hloglog' : 12 / eta ^ 2 <= Real.log (Real.log (X : Real)) :=
    twelve_div_eta_sq_le_log_log_of_exp_exp_le hloglog
  have hdelta0 : 0 <= majorArcM2LogLogDelta X := by
    unfold majorArcM2LogLogDelta
    exact inv_nonneg.mpr
      ((show (0 : Real) <= 12 / eta ^ 2 by positivity).trans hloglog')
  have hdelta : majorArcM2LogLogDelta X <= eta ^ 2 / 12 := by
    unfold majorArcM2LogLogDelta
    exact inv_log_log_le_eta_sq_div_twelve heta hloglog'
  have hJ : 1 < majorArcLogSubdivisionCount X D (k + 1) :=
    majorArcLogSubdivisionCount_one_lt hX (by omega)
  have hcJ : c.natAbs < majorArcLogSubdivisionCount X D (k + 1) :=
    majorArcFrequency_natAbs_lt_logSubdivisionCount hX (by omega) hc
  have hraw := norm_majorArcRegionWeightedPhaseSum_signed_le
    (by omega : 3 <= X) heta hsum hell hdelta0 hdelta hlarge hpower
      hqdiv hq hJ hE hc0 hcJ herror (b := b) (c := c)
  exact hraw.trans (by
    simpa [majorArcM2LogScaleCoefficient] using hscale)

private theorem self_le_ten_pow (K : Nat) : K <= 10 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ]
      have hpow : 0 < 10 ^ K := by positivity
      omega

/-- One threshold gives Eq. (11.4) for every source arity below a fixed outer
bound. The coordinate lower bound is retained from Proposition 9.1 although
the pointwise proof does not use it. -/
theorem exists_majorArcM2PointwiseLogScaleThreshold
    (D R : Nat) {eta E : Real} (heta : 0 < eta) (hE : 0 <= E) :
    ∃ K0 : Nat, ∀ K : Nat, K0 <= K ->
      ∀ k : Nat, k <= R -> ∀ a : Fin k -> Real,
      (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      ∀ b c : Int, ∀ q : Nat, 0 < q -> q ∣ 10 ^ K ->
      (q : Real) <= Real.log (((10 ^ K : Nat) : Real)) ^ D ->
      c ≠ 0 -> |(c : Real)| <= Real.log (((10 ^ K : Nat) : Real)) ^ D ->
      (∀ m ∈ Finset.Ico 1 (10 ^ K),
        projectedPrimeBoxWeightAtProduct (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) m ≠ 0 ->
        ∀ j ∈ Finset.Ico 1
          (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)),
        ∀ r ∈ majorArcReducedResidues q,
          |majorArcPrimeLogResidueSum (((10 ^ K : Nat) : Real))
              (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m j q r -
              majorArcPositiveBlockMainTerm (((10 ^ K : Nat) : Real))
                (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m q| <=
            E * majorArcPositiveBlockErrorScale (((10 ^ K : Nat) : Real))
              (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m q) ->
      ‖majorArcWeightedPhaseSum (Finset.range (10 ^ K))
        (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
          (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))
        ((b : Real) / (q : Real) +
          (c : Real) / (((10 ^ K : Nat) : Real)))‖ <=
        3 * (((10 ^ K : Nat) : Real)) /
          Real.log (((10 ^ K : Nat) : Real)) ^ (4 * D) := by
  rcases exists_majorArcM2LogScaleThreshold D R heta hE with
    ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro K hK k hk a _hlower hsum hell b c q hq hqdiv hqlog hc0 hc herror
  have hdata := hX0 (10 ^ K) (hK.trans (self_le_ten_pow K))
  rcases hdata with ⟨hX, _hlogX, hloglog, hlarge, hscale⟩
  exact norm_majorArcRegionWeightedPhaseSum_logScale_le hX heta hsum hell
    hloglog hlarge rfl hqdiv hq hqlog hE hc0 hc (hscale k hk c hc) herror

/-- The normalized contribution of the repaired second-class frequency
carrier. -/
noncomputable def majorArcClassTwoContribution
    (X : Nat) (Q : Real) (A s : Finset Nat)
    (w : Nat -> Complex) : Complex :=
  (∑ frequency ∈ majorArcClassTwoFrequencies X Q,
      majorArcWeightedPhaseSum A (fun _ => 1)
          ((frequency : Real) / (X : Real)) *
        majorArcWeightedPhaseSum s w
          (-((frequency : Real) / (X : Real)))) / (X : Complex)

/-- Pointwise digit and region bounds aggregate over the finite repaired
second class. -/
theorem norm_majorArcClassTwoContribution_le
    {X : Nat} (hX : 0 < X) (Q : Real) (A s : Finset Nat)
    (w : Nat -> Complex) {digitBound regionBound : Real}
    (hdigitBound : 0 <= digitBound) (hregionBound : 0 <= regionBound)
    (hdigit : ∀ frequency ∈ majorArcClassTwoFrequencies X Q,
      ‖majorArcWeightedPhaseSum A (fun _ => 1)
        ((frequency : Real) / (X : Real))‖ <= digitBound)
    (hregion : ∀ frequency ∈ majorArcClassTwoFrequencies X Q,
      ‖majorArcWeightedPhaseSum s w
        (-((frequency : Real) / (X : Real)))‖ <= regionBound) :
    ‖majorArcClassTwoContribution X Q A s w‖ <=
      ((majorArcClassTwoFrequencies X Q).card : Real) *
        digitBound * regionBound / (X : Real) := by
  let F := majorArcClassTwoFrequencies X Q
  let term : Nat -> Complex := fun frequency =>
    majorArcWeightedPhaseSum A (fun _ => 1)
        ((frequency : Real) / (X : Real)) *
      majorArcWeightedPhaseSum s w (-((frequency : Real) / (X : Real)))
  have hsum : ‖∑ frequency ∈ F, term frequency‖ <=
      (F.card : Real) * digitBound * regionBound := by
    calc
      ‖∑ frequency ∈ F, term frequency‖ <=
          ∑ frequency ∈ F, ‖term frequency‖ := norm_sum_le _ _
      _ <= ∑ _frequency ∈ F, digitBound * regionBound := by
        gcongr with frequency hfrequency
        dsimp [term]
        rw [norm_mul]
        exact mul_le_mul (hdigit frequency hfrequency)
          (hregion frequency hfrequency) (norm_nonneg _) hdigitBound
      _ = (F.card : Real) * digitBound * regionBound := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have _hupperNonneg : 0 <= digitBound * regionBound :=
    mul_nonneg hdigitBound hregionBound
  change ‖(∑ frequency ∈ F, term frequency) / (X : Complex)‖ <= _
  rw [norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- The repaired second-class contribution has the logarithmic saving of
Eq. (11.5), conditional on one progression-error coefficient uniform in all
eligible moduli and supported fibers. -/
theorem exists_majorArcClassTwoRegionContributionLogScaleThreshold
    (D R : Nat) {eta E : Real} (heta : 0 < eta) (hE : 0 <= E) :
    ∃ K0 : Nat, ∀ K : Nat, K0 <= K ->
      ∀ k : Nat, k <= R -> ∀ digit : Fin 10,
      ∀ a : Fin k -> Real, (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      (∀ q : Nat, 0 < q -> q ∣ 10 ^ K ->
        (q : Real) <= Real.log (((10 ^ K : Nat) : Real)) ^ D ->
        ∀ m ∈ Finset.Ico 1 (10 ^ K),
          projectedPrimeBoxWeightAtProduct (10 ^ K) a
              (majorArcM2LogLogDelta (10 ^ K)) m ≠ 0 ->
        ∀ j ∈ Finset.Ico 1
          (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)),
        ∀ r ∈ majorArcReducedResidues q,
          |majorArcPrimeLogResidueSum (((10 ^ K : Nat) : Real))
              (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m j q r -
              majorArcPositiveBlockMainTerm (((10 ^ K : Nat) : Real))
                (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m q| <=
            E * majorArcPositiveBlockErrorScale (((10 ^ K : Nat) : Real))
              (majorArcLogSubdivisionCount (10 ^ K) D (k + 1)) m q) ->
    ‖majorArcClassTwoContribution
        (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
        (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
        (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
          (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))‖ <=
      210 * ((paddedRestrictedNumbers digit K).card : Real) /
        Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  classical
  rcases exists_majorArcM2LogScaleThreshold D R heta hE with
    ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro K hK k hk digit a _hlower hsum hell herror
  have hdata := hX0 (10 ^ K) (hK.trans (self_le_ten_pow K))
  rcases hdata with ⟨hX, hlogX, hloglog, hlarge, hscale⟩
  let A := paddedRestrictedNumbers digit K
  let W : Nat -> Complex := fun n =>
    (majorArcRegionWeightAtProduct (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)
  have hdigit (frequency : Nat) :
      ‖majorArcWeightedPhaseSum A (fun _ => 1)
          ((frequency : Real) / (((10 ^ K : Nat) : Real)))‖ <=
        (A.card : Real) := by
    simpa using norm_majorArcWeightedPhaseSum_real_le_sum A
      (fun _ => (1 : Real)) (fun _ _ => zero_le_one)
      ((frequency : Real) / (((10 ^ K : Nat) : Real)))
  have hregion (frequency : Nat)
      (hfrequency : frequency ∈ majorArcClassTwoFrequencies (10 ^ K)
        (Real.log (((10 ^ K : Nat) : Real)) ^ D)) :
      ‖majorArcWeightedPhaseSum (Finset.range (10 ^ K)) W
          (-((frequency : Real) / (((10 ^ K : Nat) : Real))))‖ <=
        3 * (((10 ^ K : Nat) : Real)) /
          Real.log (((10 ^ K : Nat) : Real)) ^ (4 * D) := by
    have hclass : majorArcClassTwo (10 ^ K) frequency
        (Real.log (((10 ^ K : Nat) : Real)) ^ D) := by
      rw [majorArcClassTwoFrequencies, Finset.mem_filter] at hfrequency
      exact hfrequency.2
    rcases majorArcClassTwo.exists_signed_phase_data (by positivity) hclass with
      ⟨b, q, c, hq, _hcoprime, hqdiv, hqlog, hc0, hc, hphase⟩
    have hcNeg : |(((-c : Int) : Real))| <=
        Real.log (((10 ^ K : Nat) : Real)) ^ D := by simpa using hc
    have hphaseNeg :
        -((frequency : Real) / (((10 ^ K : Nat) : Real))) =
          ((-b : Int) : Real) / (q : Real) +
            ((-c : Int) : Real) / (((10 ^ K : Nat) : Real)) := by
      rw [hphase]
      push_cast
      ring
    rw [hphaseNeg]
    exact norm_majorArcRegionWeightedPhaseSum_logScale_le hX heta hsum hell
      hloglog hlarge rfl hqdiv hq hqlog hE (by simpa using hc0) hcNeg
      (hscale k hk (-c) hcNeg) (herror q hq hqdiv hqlog)
  have haggregate := norm_majorArcClassTwoContribution_le
    (X := 10 ^ K) (by positivity)
    (Real.log (((10 ^ K : Nat) : Real)) ^ D) A (Finset.range (10 ^ K)) W
    (digitBound := (A.card : Real))
    (regionBound := 3 * (((10 ^ K : Nat) : Real)) /
      Real.log (((10 ^ K : Nat) : Real)) ^ (4 * D))
    (by positivity) (by positivity)
    (fun frequency _ => hdigit frequency) hregion
  have hcard := majorArcClassTwoFrequencies_card_log_pow_le hX hlogX
  have hlogPos : 0 < Real.log (((10 ^ K : Nat) : Real)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 10 ^ K by omega))
  change ‖majorArcClassTwoContribution (10 ^ K)
      (Real.log (((10 ^ K : Nat) : Real)) ^ D) A (Finset.range (10 ^ K)) W‖ <= _
  calc
    ‖majorArcClassTwoContribution (10 ^ K)
        (Real.log (((10 ^ K : Nat) : Real)) ^ D) A (Finset.range (10 ^ K)) W‖ <=
      ((majorArcClassTwoFrequencies (10 ^ K)
          (Real.log (((10 ^ K : Nat) : Real)) ^ D)).card : Real) *
        (A.card : Real) *
          (3 * (((10 ^ K : Nat) : Real)) /
            Real.log (((10 ^ K : Nat) : Real)) ^ (4 * D)) /
        (((10 ^ K : Nat) : Real)) := haggregate
    _ <= (70 * Real.log (((10 ^ K : Nat) : Real)) ^ (3 * D)) *
        (A.card : Real) *
          (3 * (((10 ^ K : Nat) : Real)) /
            Real.log (((10 ^ K : Nat) : Real)) ^ (4 * D)) /
        (((10 ^ K : Nat) : Real)) := by gcongr
    _ = 210 * (A.card : Real) /
        Real.log (((10 ^ K : Nat) : Real)) ^ D := by
      rw [show 4 * D = 3 * D + D by omega, pow_add]
      field_simp
      ring

end PrimesRestrictedDigits
