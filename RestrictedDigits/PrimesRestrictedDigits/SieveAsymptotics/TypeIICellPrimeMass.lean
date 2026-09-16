import PrimesRestrictedDigits.BasicEstimates.ReciprocalPrimeChebyshev
import PrimesRestrictedDigits.MajorArcs.M2OriginalCarrier
import PrimesRestrictedDigits.MajorArcs.Subdivision
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorNormalization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Chebyshev

/-!
# Analytic mass of one Type II cell

This proves the elementary logarithmic-mass estimate used for the remainder cells in
Proposition 7.2 of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact prime carrier for one normalized-log coordinate cell. -/
noncomputable def typeIINormalizedPrimeCell
    (X : Nat) (a delta : Real) : Finset Nat :=
  (Nat.primesLE X).filter fun p =>
    normalizedPrimeLog X p ∈ Set.Ioc a (a + delta)

/-- One coordinate contributes at most `(48 / eta) * delta * log X` to the
localized logarithmic harmonic mass. -/
theorem typeIINormalizedPrimeCell_logDiv_le
    {X : Nat} {a delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta) (hdelta : 0 < delta)
    (ha : eta / 2 <= a)
    (hlarge : 2 <= (X : Real) ^ a)
    (hinv : (Real.log (X : Real))⁻¹ <= delta) :
    (typeIINormalizedPrimeCell X a delta).sum
        (fun p => Real.log (p : Real) / (p : Real)) <=
      (48 / eta) * delta * Real.log (X : Real) := by
  let x : Real := (X : Real)
  let L : Real := Real.log x
  let w : Real := x ^ a
  let z : Real := x ^ (a + 2 * delta)
  let cell := typeIINormalizedPrimeCell X a delta
  let interval :=
    (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime
  have hxOne : 1 < x := by
    dsimp only [x]
    exact_mod_cast hX
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hL : 0 < L := Real.log_pos hxOne
  have haPos : 0 < a := by linarith
  have hwTwo : 2 <= w := by simpa only [w, x] using hlarge
  have hwPos : 0 < w := by linarith
  have hzPos : 0 < z := Real.rpow_pos_of_pos hxPos _
  have hwz : w <= z := by
    dsimp only [w, z]
    exact Real.rpow_le_rpow_of_exponent_le hxOne.le (by linarith)
  have hsubset : cell ⊆ interval := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := Nat.prime_of_mem_primesLE hpData.1
    have hpBounds :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hX hpPrime _ _).mp hpData.2
    apply Finset.mem_filter.mpr
    refine ⟨mem_naturalLeftClosedRightOpenInterval.mpr ⟨hpBounds.1.le, ?_⟩,
      hpPrime⟩
    have hupper :
        x ^ (a + delta) < x ^ (a + 2 * delta) := by
      exact Real.rpow_lt_rpow_of_exponent_lt hxOne (by linarith)
    exact hpBounds.2.trans_lt (by simpa only [x, z] using hupper)
  have hreciprocalSubset :
      cell.sum (fun p => (p : Real)⁻¹) <=
        interval.sum (fun p => (p : Real)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hpInterval hpCell
    positivity
  have hChebyshev :
      interval.sum (fun p => (p : Real)⁻¹) <=
        8 / Real.log z +
          8 * Real.log (Real.log z / Real.log w) := by
    exact sum_prime_inv_halfOpen_le_chebyshev w z hwTwo hwz
  have hlogW : Real.log w = a * L := by
    dsimp only [w, L]
    exact Real.log_rpow hxPos a
  have hlogZ : Real.log z = (a + 2 * delta) * L := by
    dsimp only [z, L]
    exact Real.log_rpow hxPos (a + 2 * delta)
  have hlogWPos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogZPos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogZLower : eta / 2 * L <= Real.log z := by
    rw [hlogZ]
    exact mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hfirst : 8 / Real.log z <= 16 * delta / eta := by
    have hlogZLower' : eta * L <= 2 * Real.log z := by
      linarith
    have hinv' : L⁻¹ <= delta := by simpa only [L, x] using hinv
    rw [div_le_iff₀ hlogZPos, div_mul_eq_mul_div, le_div_iff₀ heta]
    have hscaled : 8 * eta <= 16 * delta * Real.log z := by
      have hmul := mul_le_mul_of_nonneg_left hlogZLower'
        (by positivity : 0 <= 8 * delta)
      have hdeltaL : 1 <= delta * L := by
        calc
          1 = L⁻¹ * L := by field_simp
          _ <= delta * L := mul_le_mul_of_nonneg_right hinv' hL.le
      nlinarith
    nlinarith
  have hratio : Real.log z / Real.log w = 1 + 2 * delta / a := by
    rw [hlogZ, hlogW]
    field_simp [haPos.ne', hL.ne']
  have hratioPos : 0 < 1 + 2 * delta / a := by positivity
  have hlogRatio :
      Real.log (Real.log z / Real.log w) <= 2 * delta / a := by
    rw [hratio]
    exact (Real.log_le_sub_one_of_pos hratioPos).trans_eq (by ring)
  have hsecond :
      8 * Real.log (Real.log z / Real.log w) <= 32 * delta / eta := by
    have haEta : eta <= 2 * a := by linarith
    have hratioScale : 16 * delta / a <= 32 * delta / eta := by
      rw [div_le_div_iff₀ haPos heta]
      nlinarith
    calc
      8 * Real.log (Real.log z / Real.log w) <= 8 * (2 * delta / a) := by
        exact mul_le_mul_of_nonneg_left hlogRatio (by norm_num)
      _ = 16 * delta / a := by ring
      _ <= 32 * delta / eta := hratioScale
  have hreciprocal :
      cell.sum (fun p => (p : Real)⁻¹) <= 48 * delta / eta := by
    calc
      cell.sum (fun p => (p : Real)⁻¹) <=
          interval.sum (fun p => (p : Real)⁻¹) := hreciprocalSubset
      _ <= 8 / Real.log z +
          8 * Real.log (Real.log z / Real.log w) := hChebyshev
      _ <= 16 * delta / eta + 32 * delta / eta := add_le_add hfirst hsecond
      _ = 48 * delta / eta := by ring
  have hlogTerm (p : Nat) (hp : p ∈ cell) :
      Real.log (p : Real) / (p : Real) <= L * (p : Real)⁻¹ := by
    have hpLe : p <= X :=
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
    have hpPrime :=
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hlogLe : Real.log (p : Real) <= L := by
      dsimp only [L, x]
      exact Real.log_le_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hpLe)
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    calc
      Real.log (p : Real) / (p : Real) <= L / (p : Real) :=
        div_le_div_of_nonneg_right hlogLe hpReal.le
      _ = L * (p : Real)⁻¹ := by ring
  calc
    cell.sum (fun p => Real.log (p : Real) / (p : Real)) <=
        cell.sum (fun p => L * (p : Real)⁻¹) := by
      exact Finset.sum_le_sum fun p hp => hlogTerm p hp
    _ = L * cell.sum (fun p => (p : Real)⁻¹) := by
      rw [Finset.mul_sum]
    _ <= L * (48 * delta / eta) :=
      mul_le_mul_of_nonneg_left hreciprocal hL.le
    _ = (48 / eta) * delta * Real.log (X : Real) := by
      dsimp only [L, x]
      ring

/-- The projected harmonic mass is bounded by the product of its exact
coordinate-cell masses. -/
theorem sum_projectedPrimeBoxWeight_div_le_localized
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real) :
    (Finset.range X).sum (fun m =>
      projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) <=
      Finset.univ.prod (fun i =>
        (typeIINormalizedPrimeCell X (a i) delta).sum
          (fun p => Real.log (p : Real) / (p : Real))) := by
  let cells : Fin k -> Finset Nat := fun i =>
    typeIINormalizedPrimeCell X (a i) delta
  have hsubset :
      (projectedPrimeBoxTuples X a delta).filter
          (fun p => primeTupleProduct p < X) ⊆
        Fintype.piFinset cells := by
    intro p hp
    have hpTuple := (Finset.mem_filter.mp hp).1
    rw [Fintype.mem_piFinset]
    intro i
    have hpInfo := (mem_projectedPrimeBoxTuples_iff.mp hpTuple)
    exact Finset.mem_filter.mpr ⟨hpInfo.1 i, hpInfo.2 i⟩
  unfold projectedPrimeBoxWeightAtProduct
  rw [sum_primeTupleWeightAtProduct_div_eq]
  calc
    ((projectedPrimeBoxTuples X a delta).filter
        (fun p => primeTupleProduct p < X)).sum
          (fun p => ∏ i, Real.log (p i : Real) / (p i : Real)) <=
        (Fintype.piFinset cells).sum
          (fun p => ∏ i, Real.log (p i : Real) / (p i : Real)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpPi hpNotProjected
      exact Finset.prod_nonneg fun i hi => by positivity
    _ = ∏ i, (cells i).sum
        (fun p => Real.log (p : Real) / (p : Real)) := by
      exact (Finset.prod_univ_sum cells
        (fun _i p => Real.log (p : Real) / (p : Real))).symm
    _ = ∏ i, (typeIINormalizedPrimeCell X (a i) delta).sum
        (fun p => Real.log (p : Real) / (p : Real)) := by
      rfl

/-- The last-prime logarithmic mass below the product cutoff is bounded by
Chebyshev theta. -/
theorem sum_majorArcLastPrime_log_le
    {X m k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 0 < X) (hm : 0 < m) :
    ((majorArcLastPrimes X a delta eta).filter
        (fun p => m * p < X)).sum (fun p => Real.log (p : Real)) <=
      Real.log 4 * (X : Real) / (m : Real) := by
  let source := (majorArcLastPrimes X a delta eta).filter
    (fun p => m * p < X)
  let Y : Real := (X : Real) / (m : Real)
  let target := (majorArcStrictCutoff Y).filter Nat.Prime
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hY : 0 <= Y := by
    dsimp only [Y]
    positivity
  have hsubset : source ⊆ target := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := Nat.prime_of_mem_primesLE
      (mem_majorArcLastPrimes_iff.mp hpData.1).1
    apply Finset.mem_filter.mpr
    refine ⟨mem_majorArcStrictCutoff.mpr ?_, hpPrime⟩
    rw [lt_div_iff₀ hmReal]
    have hproduct : ((m * p : Nat) : Real) < (X : Real) := by
      exact_mod_cast hpData.2
    simpa only [Nat.cast_mul, mul_comm] using hproduct
  calc
    source.sum (fun p => Real.log (p : Real)) <=
        target.sum (fun p => Real.log (p : Real)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpTarget hpSource
      exact Real.log_natCast_nonneg p
    _ <= Chebyshev.theta Y := by
      unfold Chebyshev.theta
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpCutoff, hpPrime⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨hpPrime.pos, Nat.le_floor (mem_majorArcStrictCutoff.mp hpCutoff).le⟩,
          hpPrime⟩
      · intro p hpTheta hpTarget
        exact Real.log_natCast_nonneg p
    _ <= Real.log 4 * Y := Chebyshev.theta_le_log4_mul_x hY
    _ = Real.log 4 * (X : Real) / (m : Real) := by
      dsimp only [Y]
      ring

/-- Summing the exact product-fiber factorization gives the real last-prime
convolution used by the mass estimate. -/
theorem sum_majorArcRegionWeight_eq_projected_lastPrimeLogSum
    {X k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (hX : 1 < X) :
    (Finset.range X).sum
        (majorArcRegionWeightAtProduct X a delta eta) =
      (Finset.Ico 1 X).sum (fun m =>
        projectedPrimeBoxWeightAtProduct X a delta m *
          ((majorArcLastPrimes X a delta eta).filter
            (fun p => m * p < X)).sum
              (fun p => Real.log (p : Real))) := by
  apply Complex.ofReal_injective
  simpa [majorArcWeightedPhaseSum, majorArcLastPrimePhaseSum,
    majorArcPhase] using
      (majorArcRegionWeightedPhaseSum_eq_projected_lastPrimeSum
        a delta eta 0 hX)

/-- Uniform eta-only logarithmic mass for one full major-arc cell. -/
theorem exists_typeIICellPrimeMass_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ (X k : Nat) (a : Fin k -> Real) (delta : Real),
        1 < X -> 0 < delta ->
        (Real.log (X : Real))⁻¹ <= delta ->
        (∀ i, eta / 2 <= a i) ->
        (∀ i, 2 <= (X : Real) ^ (a i)) ->
        (((k + 1 : Nat) : Real) <= 2 / eta) ->
        (Finset.range X).sum
            (majorArcRegionWeightAtProduct X a delta eta) <=
          Ceta * delta ^ k * (X : Real) *
            Real.log (X : Real) ^ k := by
  let c : Real := 48 / eta
  let base : Real := max 1 c
  let Ceta : Real := Real.log 4 * base ^ typeIIEtaArityCeiling eta
  have hcPos : 0 < c := by
    dsimp only [c]
    positivity
  have hbaseOne : 1 <= base := by
    exact le_max_left 1 c
  have hbasePos : 0 < base := zero_lt_one.trans_le hbaseOne
  have hlogFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hCeta : 0 < Ceta := by
    dsimp only [Ceta]
    exact mul_pos hlogFour (pow_pos hbasePos _)
  refine ⟨Ceta, hCeta, ?_⟩
  intro X k a delta hX hdelta hinv ha hlarge hell
  let L : Real := Real.log (X : Real)
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hX)
  have hcellNonneg (i : Fin k) :
      0 <= (typeIINormalizedPrimeCell X (a i) delta).sum
        (fun p => Real.log (p : Real) / (p : Real)) := by
    exact Finset.sum_nonneg fun p hp => by positivity
  have hcell (i : Fin k) :
      (typeIINormalizedPrimeCell X (a i) delta).sum
          (fun p => Real.log (p : Real) / (p : Real)) <=
        c * delta * L := by
    simpa only [c, L] using
      (typeIINormalizedPrimeCell_logDiv_le hX heta hdelta
        (ha i) (hlarge i) hinv)
  have hprefix :
      (Finset.range X).sum (fun m =>
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) <=
        (c * delta * L) ^ k := by
    calc
      (Finset.range X).sum (fun m =>
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) <=
          ∏ i, (typeIINormalizedPrimeCell X (a i) delta).sum
            (fun p => Real.log (p : Real) / (p : Real)) :=
        sum_projectedPrimeBoxWeight_div_le_localized X a delta
      _ <= ∏ _i : Fin k, c * delta * L := by
        exact Finset.prod_le_prod (fun i hi => hcellNonneg i)
          (fun i hi => hcell i)
      _ = (c * delta * L) ^ k := by simp
  have hweightNonneg (m : Nat) :
      0 <= projectedPrimeBoxWeightAtProduct X a delta m := by
    unfold projectedPrimeBoxWeightAtProduct
    exact primeTupleWeightAtProduct_nonneg _ _
  have hpositiveSubset : Finset.Ico 1 X ⊆ Finset.range X := by
    intro m hm
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
  have hIcoHarmonic :
      (Finset.Ico 1 X).sum (fun m =>
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) <=
        (Finset.range X).sum (fun m =>
          projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hpositiveSubset
    intro m hmRange hmIco
    exact div_nonneg (hweightNonneg m) (by positivity)
  have hcoefficientNonneg :
      0 <= Real.log 4 * (X : Real) := by positivity
  have hmass :
      (Finset.range X).sum
          (majorArcRegionWeightAtProduct X a delta eta) <=
        (Real.log 4 * (X : Real)) * (c * delta * L) ^ k := by
    rw [sum_majorArcRegionWeight_eq_projected_lastPrimeLogSum a delta eta hX]
    calc
      (Finset.Ico 1 X).sum (fun m =>
          projectedPrimeBoxWeightAtProduct X a delta m *
            ((majorArcLastPrimes X a delta eta).filter
              (fun p => m * p < X)).sum
                (fun p => Real.log (p : Real))) <=
          (Finset.Ico 1 X).sum (fun m =>
            projectedPrimeBoxWeightAtProduct X a delta m *
              (Real.log 4 * (X : Real) / (m : Real))) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (sum_majorArcLastPrime_log_le (Nat.zero_lt_of_lt hX)
            (Finset.mem_Ico.mp hm).1)
          (hweightNonneg m)
      _ = (Real.log 4 * (X : Real)) *
          (Finset.Ico 1 X).sum (fun m =>
            projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ <= (Real.log 4 * (X : Real)) *
          (Finset.range X).sum (fun m =>
            projectedPrimeBoxWeightAtProduct X a delta m / (m : Real)) :=
        mul_le_mul_of_nonneg_left hIcoHarmonic hcoefficientNonneg
      _ <= (Real.log 4 * (X : Real)) * (c * delta * L) ^ k :=
        mul_le_mul_of_nonneg_left hprefix hcoefficientNonneg
  have hellNat : k + 1 <= typeIIEtaArityCeiling eta := by
    exact_mod_cast hell.trans (Nat.le_ceil (2 / eta))
  have hkCeiling : k <= typeIIEtaArityCeiling eta :=
    (Nat.le_succ k).trans hellNat
  have hcBase : c <= base := le_max_right 1 c
  have hpow : c ^ k <= base ^ typeIIEtaArityCeiling eta := by
    exact (pow_le_pow_left₀ hcPos.le hcBase k).trans
      (pow_le_pow_right₀ hbaseOne hkCeiling)
  have hfactorNonneg :
      0 <= Real.log 4 * delta ^ k * (X : Real) * L ^ k := by positivity
  apply hmass.trans
  calc
    (Real.log 4 * (X : Real)) * (c * delta * L) ^ k =
        c ^ k * (Real.log 4 * delta ^ k * (X : Real) * L ^ k) := by
      simp only [mul_pow]
      ring
    _ <= base ^ typeIIEtaArityCeiling eta *
        (Real.log 4 * delta ^ k * (X : Real) * L ^ k) :=
      mul_le_mul_of_nonneg_right hpow hfactorNonneg
    _ = Ceta * delta ^ k * (X : Real) * Real.log (X : Real) ^ k := by
      dsimp only [Ceta, L]
      ring

end

end PrimesRestrictedDigits
