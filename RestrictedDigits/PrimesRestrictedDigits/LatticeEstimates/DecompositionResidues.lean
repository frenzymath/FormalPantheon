import PrimesRestrictedDigits.Fourier.ContinuousTransformPeriodicity
import PrimesRestrictedDigits.LatticeEstimates.DecompositionScales
import PrimesRestrictedDigits.LatticeEstimates.RationalFactorization

/-!
# Signed residues in the Lemma 14.3 decomposition

Lemma 14.1 produces signed numerators, whereas the sums in Lemma 14.3 use natural reduced
residues. This module performs the reduction together with the necessary integer grid shift
and period-one Fourier transport.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical natural reduced residue represented by a signed numerator. -/
noncomputable def signedReducedResidue
    (b : Int) (m : Nat) (hm : 0 < m) (hcop : b.natAbs.Coprime m) :
    ReducedResidue m := by
  let r : Int := b % (m : Int)
  have hr0 : 0 <= r := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have hrm : r < (m : Int) := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  let rn : Nat := r.natAbs
  have hrn : rn < m := by
    have hrm' : (rn : Int) < (m : Int) := by
      dsimp only [rn]
      rw [Int.natAbs_of_nonneg hr0]
      exact hrm
    exact_mod_cast hrm'
  refine ⟨⟨rn, hrn⟩, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
  have hgcd := Int.gcd_emod b (m : Int)
  simpa only [r, rn, Int.gcd, Int.natAbs_natCast] using hgcd.trans hcop

/-- The integer quotient removed from a signed rational numerator. -/
def signedRationalShift (b : Int) (m : Nat) : Int :=
  b / (m : Int)

/-- The aligned integer grid point obtained while reducing a signed rational
center modulo one. -/
def signedAlignedGridNumerator
    (length : Nat) (a : Fin (10 ^ length)) (b : Int) (m : Nat) : Int :=
  (a.val : Int) - signedRationalShift b m * (10 ^ length : Nat)

/-- Signed Euclidean division recovers the original numerator from its
canonical residue and quotient. -/
theorem signedReducedResidue_add_mul_shift
    (b : Int) (m : Nat) (hm : 0 < m) (hcop : b.natAbs.Coprime m) :
    ((signedReducedResidue b m hm hcop).val.val : Int) +
        (m : Int) * signedRationalShift b m = b := by
  have hraw := Int.emod_add_mul_ediv b (m : Int)
  have hresidue : ((signedReducedResidue b m hm hcop).val.val : Int) =
      b % (m : Int) := by
    dsimp only [signedReducedResidue]
    rw [Int.natCast_natAbs, abs_of_nonneg]
    exact Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  simpa only [signedRationalShift, hresidue] using hraw

/-- Reducing the rational center and shifting the grid integer preserves the
approximation error exactly. -/
theorem signedAlignedGridNumerator_phase_sub_eq
    (length : Nat) (a : Fin (10 ^ length)) (b : Int)
    (m : Nat) (hm : 0 < m) (hcop : b.natAbs.Coprime m) :
    (signedAlignedGridNumerator length a b m : Real) /
          ((10 ^ length : Nat) : Real) -
        ((signedReducedResidue b m hm hcop).val.val : Real) / (m : Real) =
      (a.val : Real) / ((10 ^ length : Nat) : Real) -
        (b : Real) / (m : Real) := by
  have hbSplitR :
      ((signedReducedResidue b m hm hcop).val.val : Real) +
          (m : Real) * signedRationalShift b m = b := by
    exact_mod_cast signedReducedResidue_add_mul_shift b m hm hcop
  dsimp only [signedAlignedGridNumerator]
  push_cast
  rw [← hbSplitR]
  field_simp
  ring

/-- The original grid frequency and its shifted representative differ by an
integer, so the normalized digit-transform magnitudes agree. -/
theorem normalizedMagnitude_signedAlignedGridNumerator
    (digit : Fin 10) (length : Nat) (a : Fin (10 ^ length))
    (b : Int) (m : Nat) :
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a.val : Real) / ((10 ^ length : Nat) : Real)) =
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((signedAlignedGridNumerator length a b m : Real) /
          ((10 ^ length : Nat) : Real)) := by
  have hperiod :=
    (normalizedPaddedDigitFourierMagnitudeAt_periodic digit length).int_mul
      (signedRationalShift b m)
  have hphase :
      (signedAlignedGridNumerator length a b m : Real) /
          ((10 ^ length : Nat) : Real) + (signedRationalShift b m : Real) =
        (a.val : Real) / ((10 ^ length : Nat) : Real) := by
    dsimp only [signedAlignedGridNumerator]
    push_cast
    field_simp
    ring
  rw [← hphase]
  simpa only [mul_one] using
    hperiod ((signedAlignedGridNumerator length a b m : Real) /
      ((10 ^ length : Nat) : Real))

/-- A signed reduced rational approximation contributes one term to the
natural reduced-residue denominator weight. -/
theorem normalizedMagnitude_le_latticeHybridDenominatorWeight
    (digit : Fin 10) (length E m : Nat) (a : Fin (10 ^ length))
    (b : Int) (hm : 0 < m) (hcop : b.natAbs.Coprime m)
    (herror :
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
        (b : Real) / (m : Real)| <=
          (E : Real) / ((10 ^ length : Nat) : Real)) :
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a.val : Real) / ((10 ^ length : Nat) : Real)) <=
      latticeHybridDenominatorWeight digit length E m := by
  classical
  let residue := signedReducedResidue b m hm hcop
  let grid := signedAlignedGridNumerator length a b m
  have hbase :
      (residue.val.val : Real) / (m : Real) ∈ Set.Icc (0 : Real) 1 := by
    have hresLe : (residue.val.val : Real) <= m := by
      exact_mod_cast residue.val.isLt.le
    exact ⟨by positivity, (div_le_one (by exact_mod_cast hm)).2 hresLe⟩
  have hgridMem : grid ∈ alignedGridWindow length (E : Real)
      ((residue.val.val : Real) / (m : Real)) := by
    rw [mem_alignedGridWindow_iff_of_mem_Icc (by positivity) hbase]
    have hphase := signedAlignedGridNumerator_phase_sub_eq
      length a b m hm hcop
    simpa only [grid, residue, hphase] using herror
  rw [normalizedMagnitude_signedAlignedGridNumerator digit length a b m]
  unfold latticeHybridDenominatorWeight alignedGridSum
  calc
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((grid : Real) / ((10 ^ length : Nat) : Real)) <=
      ∑ z ∈ alignedGridWindow length (E : Real)
          ((residue.val.val : Real) / (m : Real)),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((z : Real) / ((10 ^ length : Nat) : Real)) := by
      exact Finset.single_le_sum
        (s := alignedGridWindow length (E : Real)
          ((residue.val.val : Real) / (m : Real)))
        (f := fun z : Int => normalizedPaddedDigitFourierMagnitudeAt digit length
          ((z : Real) / ((10 ^ length : Nat) : Real)))
        (fun z _ => normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
        hgridMem
    _ <= ∑ r : ReducedResidue m,
        ∑ z ∈ alignedGridWindow length (E : Real)
            ((r.val.val : Real) / (m : Real)),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((z : Real) / ((10 ^ length : Nat) : Real)) := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (ReducedResidue m)))
        (f := fun r : ReducedResidue m =>
          ∑ z ∈ alignedGridWindow length (E : Real)
              ((r.val.val : Real) / (m : Real)),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((z : Real) / ((10 ^ length : Nat) : Real)))
        (fun r _ => Finset.sum_nonneg fun z _ =>
          normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
        (Finset.mem_univ residue)

end

end PrimesRestrictedDigits
