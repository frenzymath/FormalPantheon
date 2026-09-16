import PrimesRestrictedDigits.MajorArcs.M2OriginalCarrier
import PrimesRestrictedDigits.MajorArcs.Subdivision
import Mathlib.NumberTheory.Chebyshev

/-!
# M2 relaxation of the last-prime carrier

This implements the repaired relaxation after Eq. (11.2) of
`MAYNARD-PRD-PUBLISHED`. The original carrier has already been restricted to
reduced residues by `M2OriginalCarrier`; only those fibers are relaxed here.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- All primes below the strict relaxed cutoff `X / m`. -/
noncomputable def majorArcRelaxedLastPrimes (X m : Nat) : Finset Nat :=
  (majorArcStrictCutoff ((X : Real) / (m : Real))).filter Nat.Prime

/-- The original last-prime carrier at one projected product. -/
noncomputable def majorArcOriginalLastPrimesAt
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (m : Nat) : Finset Nat :=
  (majorArcLastPrimes X a delta eta).filter fun p => m * p < X

/-- The last primes introduced by removing both original lower bounds. -/
noncomputable def majorArcM2AddedLastPrimes
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (m : Nat) : Finset Nat :=
  majorArcRelaxedLastPrimes X m \
    majorArcOriginalLastPrimesAt X a delta eta m

/-- The two product thresholds charged in the M2 relaxation error. -/
noncomputable def majorArcM2RelaxationScale
    (X : Real) (delta eta : Real) : Real :=
  X ^ (1 - eta / 12) + X ^ (1 - delta)

/-- One reduced residue fiber of the relaxed last-prime phase sum. -/
noncomputable def majorArcRelaxedLastPrimePhaseResidueSum
    (X m q residue : Nat) (theta : Real) : Complex :=
  ∑ p ∈ (majorArcRelaxedLastPrimes X m).filter
      (fun p => p ≡ residue [MOD q]),
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)

theorem mem_majorArcRelaxedLastPrimes_iff
    {X m p : Nat} (hm : 0 < m) :
    p ∈ majorArcRelaxedLastPrimes X m <->
      p.Prime ∧ m * p < X := by
  rw [majorArcRelaxedLastPrimes, Finset.mem_filter,
    mem_majorArcStrictCutoff]
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  constructor
  · rintro ⟨hpCutoff, hpPrime⟩
    refine ⟨hpPrime, ?_⟩
    have hproduct : ((m * p : Nat) : Real) < (X : Real) := by
      rw [Nat.cast_mul]
      nlinarith [(lt_div_iff₀ hmReal).mp hpCutoff]
    exact_mod_cast hproduct
  · rintro ⟨hpPrime, hproduct⟩
    refine ⟨?_, hpPrime⟩
    rw [lt_div_iff₀ hmReal]
    exact_mod_cast (by simpa [mul_comm] using hproduct)

theorem mem_majorArcOriginalLastPrimesAt_iff
    {X k m p : Nat} {a : Fin k -> Real} {delta eta : Real} :
    p ∈ majorArcOriginalLastPrimesAt X a delta eta m <->
      p ∈ majorArcLastPrimes X a delta eta ∧ m * p < X := by
  simp [majorArcOriginalLastPrimesAt]

theorem majorArcOriginalLastPrimesAt_subset_relaxed
    {X k m : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hm : 0 < m) :
    majorArcOriginalLastPrimesAt X a delta eta m ⊆
      majorArcRelaxedLastPrimes X m := by
  intro p hp
  rw [mem_majorArcRelaxedLastPrimes_iff hm]
  rw [mem_majorArcOriginalLastPrimesAt_iff] at hp
  exact ⟨Nat.prime_of_mem_primesLE
    (mem_majorArcLastPrimes_iff.mp hp.1).1, hp.2⟩

/-- Exact membership in the added carrier. Weak original lower bounds become
strict failure alternatives. -/
theorem mem_majorArcM2AddedLastPrimes_iff
    {X k m p : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hm : 0 < m) :
    p ∈ majorArcM2AddedLastPrimes X a delta eta m <->
      p.Prime ∧ m * p < X ∧
        ((p : Real) < (X : Real) ^ (eta / 4) ∨
          (p : Real) < (X : Real) ^
            (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta)) := by
  rw [majorArcM2AddedLastPrimes, Finset.mem_sdiff,
    mem_majorArcRelaxedLastPrimes_iff hm,
    mem_majorArcOriginalLastPrimesAt_iff]
  constructor
  · rintro ⟨⟨hpPrime, hproduct⟩, hpNotOriginal⟩
    refine ⟨hpPrime, hproduct, ?_⟩
    have hpLeProduct : p ≤ m * p := Nat.le_mul_of_pos_left p hm
    have hpLeX : p ≤ X := (hpLeProduct.trans_lt hproduct).le
    have hpPrimes : p ∈ Nat.primesLE X := by
      rw [Nat.mem_primesLE]
      exact ⟨hpLeX, hpPrime⟩
    by_cases hfirst : (X : Real) ^ (eta / 4) ≤ (p : Real)
    · right
      apply lt_of_not_ge
      intro hsecond
      exact hpNotOriginal ⟨mem_majorArcLastPrimes_iff.mpr
        ⟨hpPrimes, hfirst, hsecond⟩, hproduct⟩
    · exact Or.inl (lt_of_not_ge hfirst)
  · rintro ⟨hpPrime, hproduct, hfailure⟩
    refine ⟨⟨hpPrime, hproduct⟩, ?_⟩
    rintro ⟨hpLast, _⟩
    have hpBounds := (mem_majorArcLastPrimes_iff.mp hpLast).2
    rcases hfailure with hfirst | hsecond
    · exact (not_lt_of_ge hpBounds.1) hfirst
    · exact (not_lt_of_ge hpBounds.2) hsecond

/-- Each added prime lies below one of the two sharper product thresholds. -/
theorem majorArcM2AddedLastPrime_product_lt_thresholds
    {X k m p : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hm : 0 < m)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0)
    (hp : p ∈ majorArcM2AddedLastPrimes X a delta eta m) :
    (((m * p : Nat) : Real) < (X : Real) ^ (1 - eta / 12)) ∨
      (((m * p : Nat) : Real) < (X : Real) ^ (1 - delta)) := by
  have hXreal : (1 : Real) < X := by exact_mod_cast hX
  have hXpos : (0 : Real) < X := zero_lt_one.trans hXreal
  have hmSupport := projectedPrimeBoxWeightAtProduct_support_bounds
    hX heta hsum hell hdelta0 hdelta hweight
  have hpInfo := (mem_majorArcM2AddedLastPrimes_iff hm).mp hp
  rcases hpInfo.2.2 with hpFirst | hpSecond
  · left
    have hmLt : (m : Real) < (X : Real) ^ (1 - eta / 3) :=
      hmSupport.1.trans_lt hmSupport.2
    have hpPos : (0 : Real) < p := by exact_mod_cast hpInfo.1.pos
    calc
      ((m * p : Nat) : Real) = (m : Real) * (p : Real) := by norm_cast
      _ < (X : Real) ^ (1 - eta / 3) * (p : Real) :=
        mul_lt_mul_of_pos_right hmLt hpPos
      _ < (X : Real) ^ (1 - eta / 3) * (X : Real) ^ (eta / 4) :=
        mul_lt_mul_of_pos_left hpFirst (Real.rpow_pos_of_pos hXpos _)
      _ = (X : Real) ^ (1 - eta / 12) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  · right
    calc
      ((m * p : Nat) : Real) = (m : Real) * (p : Real) := by norm_cast
      _ ≤ (X : Real) ^ ((∑ i, a i) + (k : Real) * delta) *
          (p : Real) :=
        mul_le_mul_of_nonneg_right hmSupport.1 (by positivity)
      _ < (X : Real) ^ ((∑ i, a i) + (k : Real) * delta) *
          (X : Real) ^
            (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta) :=
        mul_lt_mul_of_pos_left hpSecond (Real.rpow_pos_of_pos hXpos _)
      _ = (X : Real) ^ (1 - delta) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        push_cast
        ring

theorem majorArcM2AddedLastPrime_product_lt_relaxationScale
    {X k m p : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hm : 0 < m)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0)
    (hp : p ∈ majorArcM2AddedLastPrimes X a delta eta m) :
    ((m * p : Nat) : Real) <
      majorArcM2RelaxationScale (X : Real) delta eta := by
  have hthresholds := majorArcM2AddedLastPrime_product_lt_thresholds
    hX heta hsum hell hdelta0 hdelta hm hweight hp
  unfold majorArcM2RelaxationScale
  rcases hthresholds with hthreshold | hthreshold
  · exact hthreshold.trans_le (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
  · exact hthreshold.trans_le (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))

private theorem majorArcOriginalLastPrimesAt_residue_subset_relaxed
    {X k m q residue : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hm : 0 < m) :
    (majorArcOriginalLastPrimesAt X a delta eta m).filter
        (fun p => p ≡ residue [MOD q]) ⊆
      (majorArcRelaxedLastPrimes X m).filter
        (fun p => p ≡ residue [MOD q]) :=
  Finset.filter_subset_filter _
    (majorArcOriginalLastPrimesAt_subset_relaxed hm)

/-- Relaxed minus actual in one residue is exactly the added-prime fiber. -/
theorem majorArcRelaxedLastPrimePhaseResidueSum_sub_actual_eq_added
    {X k m q residue : Nat} {a : Fin k -> Real} {delta eta theta : Real}
    (hm : 0 < m) :
    majorArcRelaxedLastPrimePhaseResidueSum X m q residue theta -
        majorArcLastPrimePhaseResidueSum X a delta eta m q residue theta =
      ∑ p ∈ (majorArcM2AddedLastPrimes X a delta eta m).filter
          (fun p => p ≡ residue [MOD q]),
        (Real.log (p : Real) : Complex) *
          majorArcPhase (((m * p : Nat) : Real) * theta) := by
  let R := (majorArcRelaxedLastPrimes X m).filter
    (fun p => p ≡ residue [MOD q])
  let O := (majorArcOriginalLastPrimesAt X a delta eta m).filter
    (fun p => p ≡ residue [MOD q])
  let term := fun p : Nat =>
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)
  have hsubset : O ⊆ R :=
    majorArcOriginalLastPrimesAt_residue_subset_relaxed hm
  have hcarrier : R \ O =
      (majorArcM2AddedLastPrimes X a delta eta m).filter
        (fun p => p ≡ residue [MOD q]) := by
    ext p
    simp only [R, O, majorArcM2AddedLastPrimes,
      Finset.mem_sdiff, Finset.mem_filter]
    tauto
  have hactual :
      majorArcLastPrimePhaseResidueSum
          X a delta eta m q residue theta = ∑ p ∈ O, term p := by
    unfold majorArcLastPrimePhaseResidueSum
    dsimp [O, term, majorArcOriginalLastPrimesAt]
    apply Finset.sum_congr
    · ext p
      simp [and_assoc, and_left_comm]
    · intro p hp
      rfl
  unfold majorArcRelaxedLastPrimePhaseResidueSum
  change (∑ p ∈ R, term p) -
      majorArcLastPrimePhaseResidueSum
        X a delta eta m q residue theta = _
  rw [hactual, ← Finset.sum_sdiff_eq_sub hsubset, hcarrier]

private theorem majorArcM2AddedResidueFibers_pairwiseDisjoint
    {X k m q : Nat} {a : Fin k -> Real} {delta eta : Real} :
    Set.PairwiseDisjoint (majorArcReducedResidues q : Set Nat)
      (fun r => (majorArcM2AddedLastPrimes X a delta eta m).filter
        (fun p => p ≡ r [MOD q])) := by
  intro r hr s hs hrs
  change Disjoint
    ((majorArcM2AddedLastPrimes X a delta eta m).filter
      (fun p => p ≡ r [MOD q]))
    ((majorArcM2AddedLastPrimes X a delta eta m).filter
      (fun p => p ≡ s [MOD q]))
  rw [Finset.disjoint_left]
  intro p hpr hps
  have hprMod := (Finset.mem_filter.mp hpr).2
  have hpsMod := (Finset.mem_filter.mp hps).2
  have hrLt : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hsLt : s < q := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
  apply hrs
  have hrsMod : r ≡ s [MOD q] := hprMod.symm.trans hpsMod
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hrLt,
    Nat.mod_eq_of_lt hsLt] using hrsMod

private theorem sum_primeLog_majorArcStrictCutoff_le
    {Y : Real} (hY : 0 ≤ Y) :
    (∑ p ∈ (majorArcStrictCutoff Y).filter Nat.Prime,
      Real.log (p : Real)) ≤ Real.log 4 * Y := by
  calc
    (∑ p ∈ (majorArcStrictCutoff Y).filter Nat.Prime,
        Real.log (p : Real)) ≤ Chebyshev.theta Y := by
      unfold Chebyshev.theta
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpCutoff, hpPrime⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨hpPrime.pos, Nat.le_floor
            (mem_majorArcStrictCutoff.mp hpCutoff).le⟩, hpPrime⟩
      · intro p hp hnot
        exact Real.log_natCast_nonneg p
    _ ≤ Real.log 4 * Y := Chebyshev.theta_le_log4_mul_x hY

/-- The collective reduced-residue relaxation has no totient loss. -/
theorem norm_majorArcRelaxedReduced_sub_actual_le
    {X k m q : Nat} {a : Fin k -> Real} {delta eta theta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hm : 0 < m) (_hq : 0 < q)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0) :
    ‖(∑ r ∈ majorArcReducedResidues q,
        majorArcRelaxedLastPrimePhaseResidueSum X m q r theta) -
      ∑ r ∈ majorArcReducedResidues q,
        majorArcLastPrimePhaseResidueSum
          X a delta eta m q r theta‖ ≤
      Real.log 4 *
        (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) := by
  let addedFiber := fun r =>
    (majorArcM2AddedLastPrimes X a delta eta m).filter
      (fun p => p ≡ r [MOD q])
  let addedUnion := (majorArcReducedResidues q).biUnion addedFiber
  let cutoff := (majorArcStrictCutoff
    (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real))).filter
      Nat.Prime
  let term := fun p : Nat =>
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have haddedSubset : addedUnion ⊆ cutoff := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨r, hr, hpFiber⟩
    have hpAdded := (Finset.mem_filter.mp hpFiber).1
    have hpInfo := (mem_majorArcM2AddedLastPrimes_iff hm).mp hpAdded
    have hpProduct := majorArcM2AddedLastPrime_product_lt_relaxationScale
      hX heta hsum hell hdelta0 hdelta hm hweight hpAdded
    change p ∈ (majorArcStrictCutoff
      (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real))).filter
        Nat.Prime
    rw [Finset.mem_filter]
    refine ⟨mem_majorArcStrictCutoff.mpr ?_, hpInfo.1⟩
    rw [lt_div_iff₀ hmReal]
    simpa [Nat.cast_mul, mul_comm] using hpProduct
  have hpairwise :
      Set.PairwiseDisjoint (majorArcReducedResidues q : Set Nat) addedFiber :=
    majorArcM2AddedResidueFibers_pairwiseDisjoint
  have hscale : 0 ≤
      majorArcM2RelaxationScale (X : Real) delta eta / (m : Real) := by
    unfold majorArcM2RelaxationScale
    positivity
  rw [← Finset.sum_sub_distrib]
  simp_rw [majorArcRelaxedLastPrimePhaseResidueSum_sub_actual_eq_added hm]
  change ‖∑ r ∈ majorArcReducedResidues q,
    ∑ p ∈ addedFiber r, term p‖ ≤ _
  calc
    ‖∑ r ∈ majorArcReducedResidues q,
        ∑ p ∈ addedFiber r, term p‖ ≤
      ∑ r ∈ majorArcReducedResidues q,
        ‖∑ p ∈ addedFiber r, term p‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ majorArcReducedResidues q,
        ∑ p ∈ addedFiber r, ‖term p‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_sum_le _ _
    _ = ∑ r ∈ majorArcReducedResidues q,
        ∑ p ∈ addedFiber r, Real.log (p : Real) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [term]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg p), majorArcPhase,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    _ = ∑ p ∈ addedUnion, Real.log (p : Real) :=
      (Finset.sum_biUnion hpairwise).symm
    _ ≤ ∑ p ∈ cutoff, Real.log (p : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg haddedSubset
      intro p hp hnot
      exact Real.log_natCast_nonneg p
    _ ≤ Real.log 4 *
        (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real)) :=
      sum_primeLog_majorArcStrictCutoff_le hscale

private theorem projectedPrimeBoxWeightAtProduct_nonneg_relaxation
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real) (m : Nat) :
    0 ≤ projectedPrimeBoxWeightAtProduct X a delta m :=
  primeTupleWeightAtProduct_nonneg (projectedPrimeBoxTuples X a delta) m

/-- Multiplication by the projected weight removes the nonzero-support
hypothesis from the relaxation estimate. -/
theorem norm_projectedWeight_mul_reducedRelaxation_sub_le
    {X k m q : Nat} {a : Fin k -> Real} {delta eta theta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hm : 0 < m) (hq : 0 < q) :
    ‖(projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
      ((∑ r ∈ majorArcReducedResidues q,
          majorArcRelaxedLastPrimePhaseResidueSum X m q r theta) -
        ∑ r ∈ majorArcReducedResidues q,
          majorArcLastPrimePhaseResidueSum
            X a delta eta m q r theta)‖ ≤
      (Real.log 4 * majorArcM2RelaxationScale (X : Real) delta eta) *
        (projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) := by
  let W := projectedPrimeBoxWeightAtProduct X a delta m
  let difference :=
    (∑ r ∈ majorArcReducedResidues q,
      majorArcRelaxedLastPrimePhaseResidueSum X m q r theta) -
    ∑ r ∈ majorArcReducedResidues q,
      majorArcLastPrimePhaseResidueSum X a delta eta m q r theta
  have hW : 0 ≤ W :=
    projectedPrimeBoxWeightAtProduct_nonneg_relaxation X a delta m
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
  by_cases hW0 : W = 0
  · have hW0' : projectedPrimeBoxWeightAtProduct X a delta m = 0 := by
      simpa [W] using hW0
    simp [hW0, hW0']
  · calc
      W * ‖difference‖ ≤ W *
          (Real.log 4 *
            (majorArcM2RelaxationScale (X : Real) delta eta / (m : Real))) :=
        mul_le_mul_of_nonneg_left
          (norm_majorArcRelaxedReduced_sub_actual_le
            hX heta hsum hell hdelta0 hdelta hm hq hW0) hW
      _ = (Real.log 4 *
          majorArcM2RelaxationScale (X : Real) delta eta) *
            (projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) := by
        dsimp [W]
        ring

end PrimesRestrictedDigits
