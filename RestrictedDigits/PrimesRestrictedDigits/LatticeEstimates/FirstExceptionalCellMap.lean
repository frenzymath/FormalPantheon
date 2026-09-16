import PrimesRestrictedDigits.LatticeEstimates.FirstCellMap

/-!
# First-orientation exceptional fixed-cell reindexing

This is the exceptional-frequency companion to the standard first-orientation map. Its
denominator lies in both the approximation-count carrier and the coprime source band, while
its hybrid term is reused from the standard map.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The injective exceptional target attached to a first-orientation cell
pair. -/
noncomputable def latticeFirstExceptionalCellMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    LatticeExceptionalCellTarget digit length d0 d1 key.qPrimeScale
      key.g1PrimeScale key.g2Scale (key.errorScale (N * K)) := by
  let pair := a.val
  let w := latticeFirstOrientedApproximation N K delta hN hK hdelta
    hdeltaLower pair
  let f := latticeFirstOrientedFactorization N K delta hN hK hdelta
    hdeltaLower pair
  let hP := one_le_latticeApproximationScale hN hK
  let standard := latticeFirstStandardCellMap digit N K delta hN hK hdelta
    hdeltaLower key d0 d1 a
  have hcell := mem_latticeFirstScaleCell_iff.mp a.property
  have hkey : w.decompositionScaleKey hP f = key := by
    simpa only [w, f, hP, latticeFirstOrientedScaleKey] using hcell.2.2.1
  have hd0 : f.d0 = d0 := by simpa only [f] using hcell.2.2.2.1
  let m1 := d0 * (f.qPrime * f.g2)
  have hcop1 : f.b1Prime.natAbs.Coprime m1 := by
    simpa only [m1, ← hd0, Nat.mul_assoc] using f.first_reduced
  have herrors := w.errors_le_scaleKey hP f
  have herror1 :
      |(pair.val.val.1.val : Real) / ((10 ^ length : Nat) : Real) -
        (f.b1Prime : Real) / (m1 : Real)| <=
          (key.errorScale (N * K) : Real) /
            ((10 ^ length : Nat) : Real) := by
    have hraw := herrors.1
    have hratio : (w.b1 : Real) / (w.q : Real) =
        (f.b1Prime : Real) /
          ((f.d0 * f.qPrime * f.g2 : Nat) : Real) := by
      simpa only [w, Int.cast_natCast] using f.first_ratio_eq
    rw [hratio, hkey] at hraw
    simpa only [m1, hd0, Nat.mul_assoc] using hraw
  have hb1PrimeNonneg : 0 <= f.b1Prime := by
    apply f.b1Prime_nonneg
    exact_mod_cast Nat.zero_le w.b1
  have hb1PrimeCast : ((f.b1Prime.natAbs : Nat) : Real) =
      (f.b1Prime : Real) := by
    have hInt : (f.b1Prime.natAbs : Int) = f.b1Prime := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb1PrimeNonneg]
    calc
      ((f.b1Prime.natAbs : Nat) : Real) =
          ((f.b1Prime.natAbs : Int) : Real) :=
        (Int.cast_natCast f.b1Prime.natAbs).symm
      _ = (f.b1Prime : Real) := by rw [hInt]
  have herror1Nat :
      |(pair.val.val.1.val : Real) / ((10 ^ length : Nat) : Real) -
        (f.b1Prime.natAbs : Real) / (m1 : Real)| <=
          (key.errorScale (N * K) : Real) /
            ((10 ^ length : Nat) : Real) := by
    rw [hb1PrimeCast]
    exact herror1
  have hqBand : standard.1.val ∈ latticeFactorTenBand key.qPrimeScale := by
    have hqData := mem_hybridResidualSourceDenominators_iff.mp standard.1.property
    exact mem_latticeFactorTenBand_iff.mpr
      ⟨hqData.1, hqData.2.1, hqData.2.2.1⟩
  have happrox : standard.1.val ∈ latticeApproximationDenominators length
      pair.val.val.1 d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K)) := by
    change f.qPrime ∈ latticeApproximationDenominators length
      pair.val.val.1 d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K))
    rw [mem_latticeApproximationDenominators_iff]
    refine ⟨hqBand, f.b1Prime.natAbs, f.g2, ?_, ?_, ?_⟩
    · exact standard.2.2.1.property
    · simpa only [m1, Nat.mul_assoc] using hcop1
    · simpa only [m1, Nat.mul_assoc] using herror1Nat
  let firstFrequency : {a // a ∈ genericExceptionalFrequencies digit length} :=
    ⟨pair.val.val.1, hcell.1⟩
  let countedQ : {q // q ∈ latticeApproximationDenominators length
      firstFrequency.val d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K))} :=
    ⟨standard.1.val, by simpa only [firstFrequency] using happrox⟩
  let exceptionalQ : LatticeExceptionalCellDenominator length firstFrequency.val
      d0 key.qPrimeScale key.g2Scale (key.errorScale (N * K)) :=
    ⟨countedQ, standard.1.property⟩
  exact ⟨firstFrequency, ⟨exceptionalQ, standard.2.1⟩⟩

theorem latticeFirstExceptionalCellMap_firstFrequency
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeFirstExceptionalCellMap digit N K delta hN hK hdelta
      hdeltaLower key d0 d1 a).1.val = a.val.val.val.1 := by
  rfl

theorem latticeFirstExceptionalCellMap_secondGrid
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeFirstExceptionalCellMap digit N K delta hN hK hdelta
      hdeltaLower key d0 d1 a).secondGrid =
      signedAlignedGridNumerator length a.val.val.val.2
        (latticeFirstOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).b2Prime
        (((latticeFirstOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).qPrime * (d0 * d1)) *
            (latticeFirstOrientedFactorization N K delta hN hK hdelta
              hdeltaLower a.val).g1Prime) := by
  rfl

theorem latticeFirstExceptionalCellMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeFirstScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    latticeGeneratingPairWeight digit length a.val.val.val =
      latticeExceptionalCellTargetWeight digit length d0 d1 key.qPrimeScale
        key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
        (latticeFirstExceptionalCellMap digit N K delta hN hK hdelta
          hdeltaLower key d0 d1 a) := by
  simp only [latticeFirstExceptionalCellMap, latticeFirstStandardCellMap,
    latticeExceptionalCellTargetWeight, latticeSOneCellTermWeight,
    latticeHybridTermWeight_signedHybridTerm, latticeGeneratingPairWeight]

theorem latticeFirstExceptionalCellMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    Function.Injective
      (latticeFirstExceptionalCellMap digit N K delta hN hK hdelta
        hdeltaLower key d0 d1) := by
  intro a b hab
  have hfirstRaw := congrArg (fun target => target.1.val) hab
  have hgrid := congrArg LatticeExceptionalCellTarget.secondGrid hab
  rw [latticeFirstExceptionalCellMap_firstFrequency,
    latticeFirstExceptionalCellMap_firstFrequency] at hfirstRaw
  rw [latticeFirstExceptionalCellMap_secondGrid,
    latticeFirstExceptionalCellMap_secondGrid] at hgrid
  have hfirst : a.val.val.val.1 = b.val.val.val.1 := hfirstRaw
  have hsecond : a.val.val.val.2 = b.val.val.val.2 :=
    eq_of_signedAlignedGridNumerator_eq hgrid
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

/-- The first-orientation cell is bounded by the exceptional `S1*S3`
product. -/
theorem latticeFirstScaleCellMass_le_exceptional
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    latticeFirstScaleCellMass digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 <=
      latticeSOne digit length (d0 * d1) key.qPrimeScale key.g1PrimeScale
          (key.errorScale (N * K)) *
        latticeSThree digit length d0 key.qPrimeScale key.g2Scale
          (key.errorScale (N * K)) := by
  unfold latticeFirstScaleCellMass
  let source := latticeFirstScaleCell digit N K delta hN hK hdelta
    hdeltaLower key d0 d1
  let targetWeight := latticeExceptionalCellTargetWeight digit length d0 d1
    key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
  let reindex := latticeFirstExceptionalCellMap digit N K delta hN hK hdelta
    hdeltaLower key d0 d1
  calc
    (∑ a ∈ source, latticeGeneratingPairWeight digit length a.val.val) <=
        ∑ target : LatticeExceptionalCellTarget digit length d0 d1
            key.qPrimeScale key.g1PrimeScale key.g2Scale
              (key.errorScale (N * K)),
          targetWeight target := by
      exact finset_sum_le_fintype_sum_of_injective source
        (fun a => latticeGeneratingPairWeight digit length a.val.val)
        targetWeight reindex
        (latticeFirstExceptionalCellMap_injective digit N K delta hN hK hdelta
          hdeltaLower key d0 d1)
        (latticeFirstExceptionalCellMap_weight digit N K delta hN hK hdelta
          hdeltaLower key d0 d1)
        (latticeExceptionalCellTargetWeight_nonneg digit length d0 d1
          key.qPrimeScale key.g1PrimeScale key.g2Scale
          (key.errorScale (N * K)))
    _ <= latticeSOne digit length (d0 * d1) key.qPrimeScale
          key.g1PrimeScale (key.errorScale (N * K)) *
        latticeSThree digit length d0 key.qPrimeScale key.g2Scale
          (key.errorScale (N * K)) :=
      sum_latticeExceptionalCellTargetWeight_le digit length d0 d1
        key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale (N * K))

/-- The first-orientation cell satisfies the corrected common-`S1`
minimum. -/
theorem latticeFirstScaleCellMass_le_minimum
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    latticeFirstScaleCellMass digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 <=
      latticeExceptionalProductMinimum digit length d0 d1 key.qPrimeScale
        key.g1PrimeScale key.g2Scale (key.errorScale (N * K)) := by
  unfold latticeExceptionalProductMinimum
  exact le_min
    (latticeFirstScaleCellMass_le_standard digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)
    (latticeFirstScaleCellMass_le_exceptional digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)

end

end PrimesRestrictedDigits
