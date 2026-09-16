import PrimesRestrictedDigits.LatticeEstimates.SecondCellMap

/-!
# Second-orientation exceptional fixed-cell reindexing

This is the exceptional-frequency companion to the standard second-orientation map. It stores
the second original frequency, which is the first coordinate of the swapped approximation, and
recovers the first original frequency from the retained `S1` grid integer.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The injective exceptional target attached to a second-orientation cell
pair. -/
noncomputable def latticeSecondExceptionalCellMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    LatticeExceptionalCellTarget digit length d0 d1 key.qPrimeScale
      key.g1PrimeScale key.g2Scale (key.errorScale (N * K)) := by
  let pair := a.val
  let w := latticeSecondOrientedApproximation N K delta hN hK hdelta
    hdeltaLower pair
  let f := latticeSecondOrientedFactorization N K delta hN hK hdelta
    hdeltaLower pair
  let hP := one_le_latticeApproximationScale hN hK
  let standard := latticeSecondStandardCellMap digit N K delta hN hK hdelta
    hdeltaLower key d0 d1 a
  have hcell := mem_latticeSecondScaleCell_iff.mp a.property
  have hkey : w.decompositionScaleKey hP f = key := by
    simpa only [w, f, hP, latticeSecondOrientedScaleKey] using hcell.2.2.1
  have hd0 : f.d0 = d0 := by simpa only [f] using hcell.2.2.2.1
  let m1 := d0 * (f.qPrime * f.g2)
  have hcop1 : f.b1Prime.natAbs.Coprime m1 := by
    simpa only [m1, ← hd0, Nat.mul_assoc] using f.first_reduced
  have herrors := w.errors_le_scaleKey hP f
  have herror1 :
      |(pair.val.val.2.val : Real) / ((10 ^ length : Nat) : Real) -
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
      |(pair.val.val.2.val : Real) / ((10 ^ length : Nat) : Real) -
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
      pair.val.val.2 d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K)) := by
    change f.qPrime ∈ latticeApproximationDenominators length
      pair.val.val.2 d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K))
    rw [mem_latticeApproximationDenominators_iff]
    refine ⟨hqBand, f.b1Prime.natAbs, f.g2, ?_, ?_, ?_⟩
    · exact standard.2.2.1.property
    · simpa only [m1, Nat.mul_assoc] using hcop1
    · simpa only [m1, Nat.mul_assoc] using herror1Nat
  let firstFrequency : {a // a ∈ genericExceptionalFrequencies digit length} :=
    ⟨pair.val.val.2, hcell.2.1⟩
  let countedQ : {q // q ∈ latticeApproximationDenominators length
      firstFrequency.val d0 key.qPrimeScale key.g2Scale
        (key.errorScale (N * K))} :=
    ⟨standard.1.val, by simpa only [firstFrequency] using happrox⟩
  let exceptionalQ : LatticeExceptionalCellDenominator length firstFrequency.val
      d0 key.qPrimeScale key.g2Scale (key.errorScale (N * K)) :=
    ⟨countedQ, standard.1.property⟩
  exact ⟨firstFrequency, ⟨exceptionalQ, standard.2.1⟩⟩

theorem latticeSecondExceptionalCellMap_firstFrequency
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeSecondExceptionalCellMap digit N K delta hN hK hdelta
      hdeltaLower key d0 d1 a).1.val = a.val.val.val.2 := by
  rfl

theorem latticeSecondExceptionalCellMap_secondGrid
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeSecondExceptionalCellMap digit N K delta hN hK hdelta
      hdeltaLower key d0 d1 a).secondGrid =
      signedAlignedGridNumerator length a.val.val.val.1
        (latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).b2Prime
        (((latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).qPrime * (d0 * d1)) *
            (latticeSecondOrientedFactorization N K delta hN hK hdelta
              hdeltaLower a.val).g1Prime) := by
  rfl

theorem latticeSecondExceptionalCellMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    latticeGeneratingPairWeight digit length a.val.val.val =
      latticeExceptionalCellTargetWeight digit length d0 d1 key.qPrimeScale
        key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
        (latticeSecondExceptionalCellMap digit N K delta hN hK hdelta
          hdeltaLower key d0 d1 a) := by
  simp only [latticeSecondExceptionalCellMap, latticeSecondStandardCellMap,
    latticeExceptionalCellTargetWeight, latticeSOneCellTermWeight,
    latticeHybridTermWeight_signedHybridTerm, latticeGeneratingPairWeight]
  ring

theorem latticeSecondExceptionalCellMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    Function.Injective
      (latticeSecondExceptionalCellMap digit N K delta hN hK hdelta
        hdeltaLower key d0 d1) := by
  intro a b hab
  have hsecondRaw := congrArg (fun target => target.1.val) hab
  have hgrid := congrArg LatticeExceptionalCellTarget.secondGrid hab
  rw [latticeSecondExceptionalCellMap_firstFrequency,
    latticeSecondExceptionalCellMap_firstFrequency] at hsecondRaw
  rw [latticeSecondExceptionalCellMap_secondGrid,
    latticeSecondExceptionalCellMap_secondGrid] at hgrid
  have hsecond : a.val.val.val.2 = b.val.val.val.2 := hsecondRaw
  have hfirst : a.val.val.val.1 = b.val.val.val.1 :=
    eq_of_signedAlignedGridNumerator_eq hgrid
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

/-- The second-orientation cell is bounded by the exceptional `S1*S3`
product. -/
theorem latticeSecondScaleCellMass_le_exceptional
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    latticeSecondScaleCellMass digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 <=
      latticeSOne digit length (d0 * d1) key.qPrimeScale key.g1PrimeScale
          (key.errorScale (N * K)) *
        latticeSThree digit length d0 key.qPrimeScale key.g2Scale
          (key.errorScale (N * K)) := by
  unfold latticeSecondScaleCellMass
  let source := latticeSecondScaleCell digit N K delta hN hK hdelta
    hdeltaLower key d0 d1
  let targetWeight := latticeExceptionalCellTargetWeight digit length d0 d1
    key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
  let reindex := latticeSecondExceptionalCellMap digit N K delta hN hK hdelta
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
        (latticeSecondExceptionalCellMap_injective digit N K delta hN hK hdelta
          hdeltaLower key d0 d1)
        (latticeSecondExceptionalCellMap_weight digit N K delta hN hK hdelta
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

/-- The second-orientation cell satisfies the corrected common-`S1`
minimum. -/
theorem latticeSecondScaleCellMass_le_minimum
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    latticeSecondScaleCellMass digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 <=
      latticeExceptionalProductMinimum digit length d0 d1 key.qPrimeScale
        key.g1PrimeScale key.g2Scale (key.errorScale (N * K)) := by
  unfold latticeExceptionalProductMinimum
  exact le_min
    (latticeSecondScaleCellMass_le_standard digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)
    (latticeSecondScaleCellMass_le_exceptional digit N K delta hN hK hdelta
      hdeltaLower key d0 d1)

end

end PrimesRestrictedDigits
