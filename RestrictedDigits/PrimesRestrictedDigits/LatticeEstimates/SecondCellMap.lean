import PrimesRestrictedDigits.LatticeEstimates.CellTargets
import PrimesRestrictedDigits.LatticeEstimates.FactorizationRatios
import PrimesRestrictedDigits.LatticeEstimates.ScaleCells
import PrimesRestrictedDigits.LatticeEstimates.WeightedReindex

/-!
# Second-orientation fixed-cell reindexing

This file maps each selected pair in a strictly swapped-orientation scale cell injectively
into the standard weighted carrier. The first oriented coordinate is the second original
frequency, while the second oriented coordinate is the first original frequency.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The injective standard target attached to a second-orientation cell pair. -/
noncomputable def latticeSecondStandardCellMap
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    LatticeStandardCellTarget length d0 d1 key.qPrimeScale
      key.g1PrimeScale key.g2Scale (key.errorScale (N * K)) := by
  let pair := a.val
  let w := latticeSecondOrientedApproximation N K delta hN hK hdelta
    hdeltaLower pair
  let f := latticeSecondOrientedFactorization N K delta hN hK hdelta
    hdeltaLower pair
  let hP := one_le_latticeApproximationScale hN hK
  have hcell := mem_latticeSecondScaleCell_iff.mp a.property
  have hkey : w.decompositionScaleKey hP f = key := by
    simpa only [w, f, hP, latticeSecondOrientedScaleKey] using hcell.2.2.1
  have hd0 : f.d0 = d0 := by simpa only [f] using hcell.2.2.2.1
  have hd1 : f.d1 = d1 := by simpa only [f] using hcell.2.2.2.2
  have hresidual := f.mem_scaleKey_residual_bands
    (w.q_le_ten_pow_add_six hP)
  have hbands := f.mem_scaleKey_bands (w.q_le_ten_pow_add_six hP)
  have hqPrime : f.qPrime ∈ hybridResidualSourceDenominators key.qPrimeScale := by
    simpa only [← hkey, LatticePrimitiveApproximation.decompositionScaleKey]
      using hresidual.1
  have hg1Prime :
      f.g1Prime ∈ hybridResidualSourceDenominators key.g1PrimeScale := by
    simpa only [← hkey, LatticePrimitiveApproximation.decompositionScaleKey]
      using hresidual.2
  have hg2 : f.g2 ∈ latticeFactorTenBand key.g2Scale := by
    simpa only [← hkey, LatticePrimitiveApproximation.decompositionScaleKey]
      using hbands.2.2.1
  let qPrime : {q // q ∈ hybridResidualSourceDenominators key.qPrimeScale} :=
    ⟨f.qPrime, hqPrime⟩
  let g1Prime : {g // g ∈ hybridResidualSourceDenominators key.g1PrimeScale} :=
    ⟨f.g1Prime, hg1Prime⟩
  let g2 : {g // g ∈ latticeFactorTenBand key.g2Scale} := ⟨f.g2, hg2⟩
  let m1 := d0 * (f.qPrime * f.g2)
  let m2 := (f.qPrime * (d0 * d1)) * f.g1Prime
  have hm1 : 0 < m1 := by
    dsimp only [m1]
    exact Nat.mul_pos (by simpa only [← hd0] using f.d0_pos)
      (Nat.mul_pos f.qPrime_pos f.g2_pos)
  have hm2 : 0 < m2 := by
    dsimp only [m2]
    exact Nat.mul_pos
      (Nat.mul_pos f.qPrime_pos
        (Nat.mul_pos (by simpa only [← hd0] using f.d0_pos)
          (by simpa only [← hd1] using f.d1_pos)))
      f.g1Prime_pos
  have hcop1 : f.b1Prime.natAbs.Coprime m1 := by
    simpa only [m1, ← hd0, Nat.mul_assoc] using f.first_reduced
  have hcop2 : f.b2Prime.natAbs.Coprime m2 := by
    have hm2Eq : f.d0 * f.d1 * f.qPrime * f.g1Prime = m2 := by
      dsimp only [m2]
      rw [hd0, hd1]
      ring
    simpa only [← hm2Eq] using f.second_reduced
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
  have herror2 :
      |(pair.val.val.1.val : Real) / ((10 ^ length : Nat) : Real) -
        (f.b2Prime : Real) / (m2 : Real)| <=
          (key.errorScale (N * K) : Real) /
            ((10 ^ length : Nat) : Real) := by
    have hraw := herrors.2
    have hratio : (w.b2 : Real) / (w.q : Real) =
        (f.b2Prime : Real) /
          ((f.d0 * f.d1 * f.qPrime * f.g1Prime : Nat) : Real) := by
      simpa only [w, Int.cast_natCast] using f.second_ratio_eq
    rw [hratio, hkey] at hraw
    have hm2Eq : f.d0 * f.d1 * f.qPrime * f.g1Prime = m2 := by
      dsimp only [m2]
      rw [hd0, hd1]
      ring
    simpa only [hm2Eq] using hraw
  let firstTerm := signedHybridTerm length (key.errorScale (N * K)) m1
    pair.val.val.2 f.b1Prime hm1 hcop1 herror1
  let secondTerm := signedHybridTerm length (key.errorScale (N * K)) m2
    pair.val.val.1 f.b2Prime hm2 hcop2 herror2
  exact ⟨qPrime, (⟨g1Prime, secondTerm⟩, ⟨g2, firstTerm⟩)⟩

theorem latticeSecondStandardCellMap_firstGrid
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeSecondStandardCellMap digit N K delta hN hK hdelta hdeltaLower
      key d0 d1 a).firstGrid =
      signedAlignedGridNumerator length a.val.val.val.2
        (latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).b1Prime
        (d0 * ((latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).qPrime *
            (latticeSecondOrientedFactorization N K delta hN hK hdelta
              hdeltaLower a.val).g2)) := by
  rfl

theorem latticeSecondStandardCellMap_secondGrid
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    (latticeSecondStandardCellMap digit N K delta hN hK hdelta hdeltaLower
      key d0 d1 a).secondGrid =
      signedAlignedGridNumerator length a.val.val.val.1
        (latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).b2Prime
        (((latticeSecondOrientedFactorization N K delta hN hK hdelta
          hdeltaLower a.val).qPrime * (d0 * d1)) *
            (latticeSecondOrientedFactorization N K delta hN hK hdelta
              hdeltaLower a.val).g1Prime) := by
  rfl

theorem latticeSecondStandardCellMap_weight
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat)
    (a : {a // a ∈ latticeSecondScaleCell digit N K delta hN hK hdelta
      hdeltaLower key d0 d1}) :
    latticeGeneratingPairWeight digit length a.val.val.val =
      latticeStandardCellTargetWeight digit length d0 d1 key.qPrimeScale
        key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
        (latticeSecondStandardCellMap digit N K delta hN hK hdelta
          hdeltaLower key d0 d1 a) := by
  simp only [latticeSecondStandardCellMap, latticeStandardCellTargetWeight,
    latticeSOneCellTermWeight, latticeSTwoCellTermWeight,
    latticeHybridTermWeight_signedHybridTerm, latticeGeneratingPairWeight]

theorem latticeSecondStandardCellMap_injective
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    Function.Injective
      (latticeSecondStandardCellMap digit N K delta hN hK hdelta
        hdeltaLower key d0 d1) := by
  intro a b hab
  have hfirstGrid := congrArg LatticeStandardCellTarget.firstGrid hab
  have hsecondGrid := congrArg LatticeStandardCellTarget.secondGrid hab
  rw [latticeSecondStandardCellMap_firstGrid,
    latticeSecondStandardCellMap_firstGrid] at hfirstGrid
  rw [latticeSecondStandardCellMap_secondGrid,
    latticeSecondStandardCellMap_secondGrid] at hsecondGrid
  have hsecond : a.val.val.val.2 = b.val.val.val.2 :=
    eq_of_signedAlignedGridNumerator_eq hfirstGrid
  have hfirst : a.val.val.val.1 = b.val.val.val.1 :=
    eq_of_signedAlignedGridNumerator_eq hsecondGrid
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

/-- The second-orientation cell is bounded by the standard `S1*S2` product. -/
theorem latticeSecondScaleCellMass_le_standard
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (key : LatticeDecompositionScaleKey length) (d0 d1 : Nat) :
    latticeSecondScaleCellMass digit N K delta hN hK hdelta hdeltaLower
        key d0 d1 <=
      latticeSOne digit length (d0 * d1) key.qPrimeScale key.g1PrimeScale
          (key.errorScale (N * K)) *
        latticeSTwo digit length d0 key.qPrimeScale key.g2Scale
          (key.errorScale (N * K)) := by
  unfold latticeSecondScaleCellMass
  let source := latticeSecondScaleCell digit N K delta hN hK hdelta
    hdeltaLower key d0 d1
  let targetWeight := latticeStandardCellTargetWeight digit length d0 d1
    key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale (N * K))
  let reindex := latticeSecondStandardCellMap digit N K delta hN hK hdelta
    hdeltaLower key d0 d1
  calc
    (∑ a ∈ source, latticeGeneratingPairWeight digit length a.val.val) <=
        ∑ target : LatticeStandardCellTarget length d0 d1 key.qPrimeScale
            key.g1PrimeScale key.g2Scale (key.errorScale (N * K)),
          targetWeight target := by
      exact finset_sum_le_fintype_sum_of_injective source
        (fun a => latticeGeneratingPairWeight digit length a.val.val)
        targetWeight reindex
        (latticeSecondStandardCellMap_injective digit N K delta hN hK hdelta
          hdeltaLower key d0 d1)
        (latticeSecondStandardCellMap_weight digit N K delta hN hK hdelta
          hdeltaLower key d0 d1)
        (latticeStandardCellTargetWeight_nonneg digit length d0 d1
          key.qPrimeScale key.g1PrimeScale key.g2Scale
          (key.errorScale (N * K)))
    _ <= latticeSOne digit length (d0 * d1) key.qPrimeScale
          key.g1PrimeScale (key.errorScale (N * K)) *
        latticeSTwo digit length d0 key.qPrimeScale key.g2Scale
          (key.errorScale (N * K)) :=
      sum_latticeStandardCellTargetWeight_le digit length d0 d1
        key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale (N * K))

end

end PrimesRestrictedDigits
