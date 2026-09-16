import PrimesRestrictedDigits.LatticeEstimates.DecompositionResidues

/-!
# Individual hybrid summands for weighted reindexing

An element of `LatticeHybridTerm` is one reduced residue together with one aligned
integer-grid point. Making this finite carrier explicit permits the injective weighted
reindexing required in the repaired Lemma 14.3 proof.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- One summand in `latticeHybridDenominatorWeight`. -/
abbrev LatticeHybridTerm (length E m : Nat) :=
  Σ residue : ReducedResidue m,
    {grid : Int // grid ∈ alignedGridWindow length (E : Real)
      ((residue.val.val : Real) / (m : Real))}

/-- The Fourier weight of one explicit hybrid summand. -/
def latticeHybridTermWeight
    (digit : Fin 10) (length E m : Nat) (term : LatticeHybridTerm length E m) :
    Real :=
  normalizedPaddedDigitFourierMagnitudeAt digit length
    ((term.2.val : Real) / ((10 ^ length : Nat) : Real))

theorem latticeHybridTermWeight_nonneg
    (digit : Fin 10) (length E m : Nat) (term : LatticeHybridTerm length E m) :
    0 <= latticeHybridTermWeight digit length E m term :=
  normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _

/-- Summing the explicit term carrier recovers the nested source sum. -/
theorem sum_latticeHybridTermWeight
    (digit : Fin 10) (length E m : Nat) :
    (∑ term : LatticeHybridTerm length E m,
      latticeHybridTermWeight digit length E m term) =
        latticeHybridDenominatorWeight digit length E m := by
  classical
  unfold latticeHybridDenominatorWeight alignedGridSum
    latticeHybridTermWeight LatticeHybridTerm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro residue _
  exact (Finset.sum_subtype (M := Real)
    (alignedGridWindow length (E : Real)
      ((residue.val.val : Real) / (m : Real)))
    (fun _ => Iff.rfl)
    (fun grid : Int => normalizedPaddedDigitFourierMagnitudeAt digit length
      ((grid : Real) / ((10 ^ length : Nat) : Real)))).symm

/-- The aligned integer has the same residue modulo the outer grid size as
the original `Fin` frequency. -/
theorem signedAlignedGridNumerator_emod
    (length : Nat) (a : Fin (10 ^ length)) (b : Int) (m : Nat) :
    signedAlignedGridNumerator length a b m % (10 ^ length : Nat) =
      (a.val : Int) := by
  have hXPos : (0 : Int) < (10 ^ length : Nat) := by positivity
  have haNonneg : (0 : Int) <= a.val := by positivity
  have haLt : (a.val : Int) < (10 ^ length : Nat) := by
    exact_mod_cast a.isLt
  unfold signedAlignedGridNumerator
  rw [Int.sub_emod, Int.mul_emod]
  simp only [Int.emod_self, mul_zero, Int.zero_emod, sub_zero, Int.emod_emod]
  exact Int.emod_eq_of_lt haNonneg haLt

/-- Equality of shifted grid integers recovers equality of the original
finite-grid frequencies, even when the signed rational centers differ. -/
theorem eq_of_signedAlignedGridNumerator_eq
    {length : Nat} {a a' : Fin (10 ^ length)} {b b' : Int} {m m' : Nat}
    (hgrid : signedAlignedGridNumerator length a b m =
      signedAlignedGridNumerator length a' b' m') :
    a = a' := by
  apply Fin.ext
  have hmod := congrArg (fun z : Int => z % (10 ^ length : Nat)) hgrid
  have hvals : (a.val : Int) = (a'.val : Int) := by
    simpa only [signedAlignedGridNumerator_emod] using hmod
  exact_mod_cast hvals

/-- A signed reduced approximation determines one explicit hybrid summand. -/
noncomputable def signedHybridTerm
    (length E m : Nat) (a : Fin (10 ^ length)) (b : Int)
    (hm : 0 < m) (hcop : b.natAbs.Coprime m)
    (herror :
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
        (b : Real) / (m : Real)| <=
          (E : Real) / ((10 ^ length : Nat) : Real)) :
    LatticeHybridTerm length E m := by
  let residue := signedReducedResidue b m hm hcop
  let grid := signedAlignedGridNumerator length a b m
  refine ⟨residue, ⟨grid, ?_⟩⟩
  have hbase :
      (residue.val.val : Real) / (m : Real) ∈ Set.Icc (0 : Real) 1 := by
    have hresLe : (residue.val.val : Real) <= m := by
      exact_mod_cast residue.val.isLt.le
    exact ⟨by positivity, (div_le_one (by exact_mod_cast hm)).2 hresLe⟩
  rw [mem_alignedGridWindow_iff_of_mem_Icc (by positivity) hbase]
  have hphase := signedAlignedGridNumerator_phase_sub_eq
    length a b m hm hcop
  simpa only [grid, residue, hphase] using herror

/-- The term selected from a signed approximation has exactly the original
Fourier weight. -/
theorem latticeHybridTermWeight_signedHybridTerm
    (digit : Fin 10) (length E m : Nat) (a : Fin (10 ^ length)) (b : Int)
    (hm : 0 < m) (hcop : b.natAbs.Coprime m)
    (herror :
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
        (b : Real) / (m : Real)| <=
          (E : Real) / ((10 ^ length : Nat) : Real)) :
    latticeHybridTermWeight digit length E m
        (signedHybridTerm length E m a b hm hcop herror) =
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a.val : Real) / ((10 ^ length : Nat) : Real)) := by
  symm
  exact normalizedMagnitude_signedAlignedGridNumerator digit length a b m

end

end PrimesRestrictedDigits
