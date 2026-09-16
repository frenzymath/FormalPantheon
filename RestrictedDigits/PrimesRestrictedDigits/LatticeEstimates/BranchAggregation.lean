import PrimesRestrictedDigits.LatticeEstimates.CellAggregationTarget
import PrimesRestrictedDigits.LatticeEstimates.FirstExceptionalCellMap
import PrimesRestrictedDigits.LatticeEstimates.OrientationMass
import PrimesRestrictedDigits.LatticeEstimates.SecondExceptionalCellMap

/-!
# Aggregation within each Lemma 14.3 orientation

Each exceptional oriented pair is sent to its admissible five-scale key, its two actual
decimal-smooth factors, and the certified fixed-cell member. The retained pair makes the map
injective.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

abbrev LatticeFirstScaleAggregationTarget
    (digit : Fin 10) (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  LatticeScaleAggregationTarget length (N * K)
    (LatticeFirstOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower)
    (fun key d0 d1 => latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)

noncomputable def latticeFirstScaleAggregationMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    LatticeFirstScaleAggregationTarget digit length N K delta
      hN hK hdelta hdeltaLower := by
  let pair := a.val
  let w := latticeFirstOrientedApproximation N K delta hN hK hdelta
    hdeltaLower pair
  let f := latticeFirstOrientedFactorization N K delta hN hK hdelta
    hdeltaLower pair
  let hP := one_le_latticeApproximationScale hN hK
  let key := latticeFirstOrientedScaleKey N K delta hN hK hdelta
    hdeltaLower pair
  have hadmissible : key.IsAdmissible (N * K) := by
    simpa only [key, latticeFirstOrientedScaleKey, w, f, hP] using
      w.scaleKey_isAdmissible hP f
  let keyIndex : {key // key ∈
      LatticeDecompositionScaleKey.admissibleCarrier length (N * K)} :=
    ⟨key, LatticeDecompositionScaleKey.mem_admissibleCarrier_iff.mpr
      hadmissible⟩
  have hsmooth := f.mem_scaleKey_smooth_bands (w.q_le_ten_pow_add_six hP)
  have hd0Mem : f.d0 ∈ latticeSmoothFactorTenBand key.d0Scale := by
    simpa only [key, latticeFirstOrientedScaleKey, w, f, hP,
      LatticePrimitiveApproximation.decompositionScaleKey] using hsmooth.1
  have hd1Mem : f.d1 ∈ latticeSmoothFactorTenBand key.d1Scale := by
    simpa only [key, latticeFirstOrientedScaleKey, w, f, hP,
      LatticePrimitiveApproximation.decompositionScaleKey] using hsmooth.2
  let d0Index : {d // d ∈ latticeSmoothFactorTenBand keyIndex.val.d0Scale} :=
    ⟨f.d0, by simpa only [keyIndex] using hd0Mem⟩
  let d1Index : {d // d ∈ latticeSmoothFactorTenBand keyIndex.val.d1Scale} :=
    ⟨f.d1, by simpa only [keyIndex] using hd1Mem⟩
  have hcell : pair ∈ latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower keyIndex.val d0Index.val d1Index.val := by
    apply mem_latticeFirstScaleCell_iff.mpr
    exact ⟨a.property.1, a.property.2, rfl, rfl, rfl⟩
  exact ⟨keyIndex, ⟨d0Index, ⟨d1Index, ⟨pair, hcell⟩⟩⟩⟩

theorem latticeFirstScaleAggregationMap_source
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    latticeScaleAggregationTargetSource
      (latticeFirstScaleAggregationMap digit N K delta hN hK hdelta
        hdeltaLower a) = a.val := by
  rfl

theorem latticeFirstScaleAggregationMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    Function.Injective
      (latticeFirstScaleAggregationMap digit N K delta hN hK hdelta
        hdeltaLower) := by
  intro a b hab
  apply Subtype.ext
  have hsource := congrArg latticeScaleAggregationTargetSource hab
  simpa only [latticeFirstScaleAggregationMap_source] using hsource

theorem latticeFirstScaleAggregationMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeFirstExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    latticeGeneratingPairWeight digit length a.val.val.val =
      latticeScaleAggregationTargetWeight
        (fun pair : LatticeFirstOrientedGeneratingPair length N K delta
          hN hK hdelta hdeltaLower =>
            latticeGeneratingPairWeight digit length pair.val.val)
        (latticeFirstScaleAggregationMap digit N K delta hN hK hdelta
          hdeltaLower a) := by
  rfl

/-- One orientation costs at most the five-scale carrier cardinality times a
uniform smooth-pair majorant. -/
theorem latticeFirstOrientedExceptionalMass_le
    (digit : Fin 10) {length : Nat} (N K delta B : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (hB : 0 <= B)
    (hmajorant : ∀ key,
      key ∈ LatticeDecompositionScaleKey.admissibleCarrier length (N * K) ->
      latticeExceptionalSmoothPairSum digit length key.qPrimeScale
        key.g1PrimeScale key.g2Scale key.d0Scale key.d1Scale
          (key.errorScale (N * K)) <= B) :
    latticeFirstOrientedExceptionalMass digit N K delta hN hK hdelta
        hdeltaLower <= ((length + 7) ^ 5 : Nat) * B := by
  let alpha := LatticeFirstOrientedGeneratingPair length N K delta
    hN hK hdelta hdeltaLower
  let cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha :=
    fun key d0 d1 => latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1
  let sourceWeight : alpha -> Real := fun pair =>
    latticeGeneratingPairWeight digit length pair.val.val
  let targetWeight : LatticeScaleAggregationTarget length (N * K) alpha cell ->
      Real := latticeScaleAggregationTargetWeight sourceWeight
  calc
    latticeFirstOrientedExceptionalMass digit N K delta hN hK hdelta
        hdeltaLower <=
      ∑ target : LatticeScaleAggregationTarget length (N * K) alpha cell,
        targetWeight target := by
      exact fintype_sum_le_fintype_sum_of_injective
        (fun a : LatticeFirstExceptionalOrientedPair digit length N K delta
          hN hK hdelta hdeltaLower =>
            latticeGeneratingPairWeight digit length a.val.val.val)
        targetWeight
        (latticeFirstScaleAggregationMap digit N K delta hN hK hdelta
          hdeltaLower)
        (latticeFirstScaleAggregationMap_injective digit N K delta hN hK
          hdelta hdeltaLower)
        (latticeFirstScaleAggregationMap_weight digit N K delta hN hK hdelta
          hdeltaLower)
        (latticeScaleAggregationTargetWeight_nonneg
          (fun pair : alpha => latticeGeneratingPairWeight_nonneg digit length
            pair.val.val))
    _ <= (LatticeDecompositionScaleKey.admissibleCarrier length (N * K)).card *
        B := by
      apply sum_latticeScaleAggregationTargetWeight_le digit length (N * K) B
        alpha cell sourceWeight
      · intro key d0 d1 hd0 hd1
        exact latticeFirstScaleCellMass_le_minimum digit N K delta hN hK hdelta
          hdeltaLower key d0 d1
      · exact hmajorant
    _ <= ((length + 7) ^ 5 : Nat) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast LatticeDecompositionScaleKey.card_admissibleCarrier_le
        length (N * K)

abbrev LatticeSecondScaleAggregationTarget
    (digit : Fin 10) (length : Nat) (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :=
  LatticeScaleAggregationTarget length (N * K)
    (LatticeSecondOrientedGeneratingPair length N K delta
      hN hK hdelta hdeltaLower)
    (fun key d0 d1 => latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)

noncomputable def latticeSecondScaleAggregationMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    LatticeSecondScaleAggregationTarget digit length N K delta
      hN hK hdelta hdeltaLower := by
  let pair := a.val
  let w := latticeSecondOrientedApproximation N K delta hN hK hdelta
    hdeltaLower pair
  let f := latticeSecondOrientedFactorization N K delta hN hK hdelta
    hdeltaLower pair
  let hP := one_le_latticeApproximationScale hN hK
  let key := latticeSecondOrientedScaleKey N K delta hN hK hdelta
    hdeltaLower pair
  have hadmissible : key.IsAdmissible (N * K) := by
    simpa only [key, latticeSecondOrientedScaleKey, w, f, hP] using
      w.scaleKey_isAdmissible hP f
  let keyIndex : {key // key ∈
      LatticeDecompositionScaleKey.admissibleCarrier length (N * K)} :=
    ⟨key, LatticeDecompositionScaleKey.mem_admissibleCarrier_iff.mpr
      hadmissible⟩
  have hsmooth := f.mem_scaleKey_smooth_bands (w.q_le_ten_pow_add_six hP)
  have hd0Mem : f.d0 ∈ latticeSmoothFactorTenBand key.d0Scale := by
    simpa only [key, latticeSecondOrientedScaleKey, w, f, hP,
      LatticePrimitiveApproximation.decompositionScaleKey] using hsmooth.1
  have hd1Mem : f.d1 ∈ latticeSmoothFactorTenBand key.d1Scale := by
    simpa only [key, latticeSecondOrientedScaleKey, w, f, hP,
      LatticePrimitiveApproximation.decompositionScaleKey] using hsmooth.2
  let d0Index : {d // d ∈ latticeSmoothFactorTenBand keyIndex.val.d0Scale} :=
    ⟨f.d0, by simpa only [keyIndex] using hd0Mem⟩
  let d1Index : {d // d ∈ latticeSmoothFactorTenBand keyIndex.val.d1Scale} :=
    ⟨f.d1, by simpa only [keyIndex] using hd1Mem⟩
  have hcell : pair ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower keyIndex.val d0Index.val d1Index.val := by
    apply mem_latticeSecondScaleCell_iff.mpr
    exact ⟨a.property.1, a.property.2, rfl, rfl, rfl⟩
  exact ⟨keyIndex, ⟨d0Index, ⟨d1Index, ⟨pair, hcell⟩⟩⟩⟩

theorem latticeSecondScaleAggregationMap_source
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    latticeScaleAggregationTargetSource
      (latticeSecondScaleAggregationMap digit N K delta hN hK hdelta
        hdeltaLower a) = a.val := by
  rfl

theorem latticeSecondScaleAggregationMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    Function.Injective
      (latticeSecondScaleAggregationMap digit N K delta hN hK hdelta
        hdeltaLower) := by
  intro a b hab
  apply Subtype.ext
  have hsource := congrArg latticeScaleAggregationTargetSource hab
  simpa only [latticeSecondScaleAggregationMap_source] using hsource

theorem latticeSecondScaleAggregationMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (a : LatticeSecondExceptionalOrientedPair digit length N K delta
      hN hK hdelta hdeltaLower) :
    latticeGeneratingPairWeight digit length a.val.val.val =
      latticeScaleAggregationTargetWeight
        (fun pair : LatticeSecondOrientedGeneratingPair length N K delta
          hN hK hdelta hdeltaLower =>
            latticeGeneratingPairWeight digit length pair.val.val)
        (latticeSecondScaleAggregationMap digit N K delta hN hK hdelta
          hdeltaLower a) := by
  rfl

theorem latticeSecondOrientedExceptionalMass_le
    (digit : Fin 10) {length : Nat} (N K delta B : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (hB : 0 <= B)
    (hmajorant : ∀ key,
      key ∈ LatticeDecompositionScaleKey.admissibleCarrier length (N * K) ->
      latticeExceptionalSmoothPairSum digit length key.qPrimeScale
        key.g1PrimeScale key.g2Scale key.d0Scale key.d1Scale
          (key.errorScale (N * K)) <= B) :
    latticeSecondOrientedExceptionalMass digit N K delta hN hK hdelta
        hdeltaLower <= ((length + 7) ^ 5 : Nat) * B := by
  let alpha := LatticeSecondOrientedGeneratingPair length N K delta
    hN hK hdelta hdeltaLower
  let cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha :=
    fun key d0 d1 => latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1
  let sourceWeight : alpha -> Real := fun pair =>
    latticeGeneratingPairWeight digit length pair.val.val
  let targetWeight : LatticeScaleAggregationTarget length (N * K) alpha cell ->
      Real := latticeScaleAggregationTargetWeight sourceWeight
  calc
    latticeSecondOrientedExceptionalMass digit N K delta hN hK hdelta
        hdeltaLower <=
      ∑ target : LatticeScaleAggregationTarget length (N * K) alpha cell,
        targetWeight target := by
      exact fintype_sum_le_fintype_sum_of_injective
        (fun a : LatticeSecondExceptionalOrientedPair digit length N K delta
          hN hK hdelta hdeltaLower =>
            latticeGeneratingPairWeight digit length a.val.val.val)
        targetWeight
        (latticeSecondScaleAggregationMap digit N K delta hN hK hdelta
          hdeltaLower)
        (latticeSecondScaleAggregationMap_injective digit N K delta hN hK
          hdelta hdeltaLower)
        (latticeSecondScaleAggregationMap_weight digit N K delta hN hK hdelta
          hdeltaLower)
        (latticeScaleAggregationTargetWeight_nonneg
          (fun pair : alpha => latticeGeneratingPairWeight_nonneg digit length
            pair.val.val))
    _ <= (LatticeDecompositionScaleKey.admissibleCarrier length (N * K)).card *
        B := by
      apply sum_latticeScaleAggregationTargetWeight_le digit length (N * K) B
        alpha cell sourceWeight
      · intro key d0 d1 hd0 hd1
        exact latticeSecondScaleCellMass_le_minimum digit N K delta hN hK
          hdelta hdeltaLower key d0 d1
      · exact hmajorant
    _ <= ((length + 7) ^ 5 : Nat) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast LatticeDecompositionScaleKey.card_admissibleCarrier_le
        length (N * K)

end

end PrimesRestrictedDigits
