import PrimesRestrictedDigits.MajorArcs.Partition
import PrimesRestrictedDigits.MajorArcs.Phase
import PrimesRestrictedDigits.MajorArcs.PositiveBlock

/-!
# Signed M2 phase sums on one positive block

This records the signed affine data and the pointwise-to-scalar finite transfer
used in the M2 calculation on published pp. 186--188. The progression estimate
remains an explicit input to later modules.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A repaired class-two frequency has signed rational phase data with a
nonzero integral offset. -/
theorem majorArcClassTwo.exists_signed_phase_data
    {X frequency : Nat} {Q : Real} (hX : 0 < X)
    (hclass : majorArcClassTwo X frequency Q) :
    ∃ b : Int, ∃ q : Nat, ∃ c : Int,
      0 < q ∧ Nat.Coprime b.natAbs q ∧ q ∣ X ∧
        (q : Real) ≤ Q ∧ c ≠ 0 ∧ |(c : Real)| ≤ Q ∧
        (frequency : Real) / (X : Real) =
          (b : Real) / (q : Real) + (c : Real) / (X : Real) := by
  rcases majorArcDivisorNonzeroApproximation.offset hX hclass.divisorNonzero with
    ⟨r, hr, hden, hoffset, hbound⟩
  refine ⟨r.num, r.den, majorArcSignedOffset X frequency r, r.den_pos,
    r.reduced, hden, hr.2, hoffset, hbound, ?_⟩
  have hidentityRat := majorArcSignedOffset_identity
    (a := frequency) hX hden
  have hidentityReal := congrArg (fun z : Rat => (z : Real)) hidentityRat
  calc
    (frequency : Real) / (X : Real) =
        (r : Real) + (majorArcSignedOffset X frequency r : Real) /
          (X : Real) := by
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
        Rat.cast_intCast] using hidentityReal
    _ = (r.num : Real) / (r.den : Real) +
        (majorArcSignedOffset X frequency r : Real) / (X : Real) := by
      rw [Rat.cast_def]

/-- The prime-log phase sum in one positive block and one residue class. -/
noncomputable def majorArcSignedPrimePhaseResidueSum
    (X : Real) (J m j q residue : Nat) (b c : Int) : Complex :=
  ∑ p ∈ ((majorArcBlock X J m j).filter
      (fun n => n ≡ residue [MOD q])).filter Nat.Prime,
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) *
        ((b : Real) / (q : Real) + (c : Real) / X))

/-- On one residue fiber, phase linearization and a scalar prime-log estimate
give the complete complex error. -/
theorem norm_majorArcSignedPrimePhaseResidueSum_sub_main_le
    {X M : Real} {J m j q residue : Nat} {b c : Int}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) (hq : 0 < q) :
    ‖majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
      majorArcPhase
          ((b : Real) * (residue : Real) * (m : Real) / (q : Real)) *
        majorArcPhase
          ((j : Real) * majorArcSubdivisionWidth J * (c : Real)) *
        (M : Complex)‖ ≤
      2 * Real.pi * |(c : Real)| * majorArcSubdivisionWidth J *
          majorArcPrimeLogResidueSum X J m j q residue +
        |majorArcPrimeLogResidueSum X J m j q residue - M| := by
  let s := ((majorArcBlock X J m j).filter
    (fun n => n ≡ residue [MOD q])).filter Nat.Prime
  let phase := majorArcPhase
      ((b : Real) * (residue : Real) * (m : Real) / (q : Real)) *
    majorArcPhase
      ((j : Real) * majorArcSubdivisionWidth J * (c : Real))
  let A := majorArcPrimeLogResidueSum X J m j q residue
  let E := 2 * Real.pi * |(c : Real)| * majorArcSubdivisionWidth J
  have hAcast :
      (A : Complex) =
        ∑ p ∈ s, (Real.log (p : Real) : Complex) := by
    unfold A majorArcPrimeLogResidueSum
    dsimp [s]
    push_cast
    rfl
  have hsum :
      majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
          phase * (A : Complex) =
        ∑ p ∈ s, (Real.log (p : Real) : Complex) *
          (majorArcPhase (((m * p : Nat) : Real) *
              ((b : Real) / (q : Real) + (c : Real) / X)) - phase) := by
    unfold majorArcSignedPrimePhaseResidueSum
    dsimp [s]
    rw [hAcast]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hlinear :
      ‖majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
          phase * (A : Complex)‖ ≤ E * A := by
    rw [hsum]
    calc
      ‖∑ p ∈ s, (Real.log (p : Real) : Complex) *
          (majorArcPhase (((m * p : Nat) : Real) *
              ((b : Real) / (q : Real) + (c : Real) / X)) - phase)‖ ≤
          ∑ p ∈ s, ‖(Real.log (p : Real) : Complex) *
            (majorArcPhase (((m * p : Nat) : Real) *
                ((b : Real) / (q : Real) + (c : Real) / X)) - phase)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ s, Real.log (p : Real) * E := by
        apply Finset.sum_le_sum
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpResidue, _hpPrime⟩
        rcases Finset.mem_filter.mp hpResidue with ⟨hpBlock, hpMod⟩
        have hphase := majorArcBlock_phase_error_le_int
          (b := b) (c := c) hX hJ hm hpBlock hq hpMod
        dsimp [phase, E] at hphase ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_natCast_nonneg p)]
        exact mul_le_mul_of_nonneg_left hphase (Real.log_natCast_nonneg p)
      _ = E * A := by
        unfold A majorArcPrimeLogResidueSum
        dsimp [s]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hphaseNorm : ‖phase‖ = 1 := by
    dsimp [phase]
    rw [norm_mul, majorArcPhase, majorArcPhase,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hscalar :
      ‖phase * (A : Complex) - phase * (M : Complex)‖ = |A - M| := by
    rw [← mul_sub, norm_mul, hphaseNorm]
    rw [one_mul, show (A : Complex) - (M : Complex) =
      ((A - M : Real) : Complex) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
        phase * (M : Complex)‖ ≤
        ‖majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
          phase * (A : Complex)‖ +
        ‖phase * (A : Complex) - phase * (M : Complex)‖ :=
      calc
        _ = ‖(majorArcSignedPrimePhaseResidueSum X J m j q residue b c -
            phase * (A : Complex)) +
            (phase * (A : Complex) - phase * (M : Complex))‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    _ ≤ E * A + |A - M| := add_le_add hlinear hscalar.le
    _ = _ := rfl

end PrimesRestrictedDigits
