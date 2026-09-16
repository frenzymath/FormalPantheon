import PrimesRestrictedDigits.MajorArcs.M2Relaxation
import PrimesRestrictedDigits.MajorArcs.M2Phase
import PrimesRestrictedDigits.MajorArcs.ZeroBlock

/-!
# Subdivision of the relaxed M2 carrier

The strict relaxed prime cutoff is partitioned into every half-open block,
including block zero. The zero block is then bounded collectively over reduced
residues, so no totient factor is introduced.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The prime-log phase sum on one block and one residue at an arbitrary real
phase. -/
noncomputable def majorArcPrimePhaseResidueBlockSum
    (X : Real) (J m j q residue : Nat) (theta : Real) : Complex :=
  ∑ p ∈ ((majorArcBlock X J m j).filter
      (fun n => n ≡ residue [MOD q])).filter Nat.Prime,
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)

/-- One relaxed residue fiber is exactly the sum of all its subdivision
blocks. The phase is arbitrary and the strict upper endpoint is retained. -/
theorem majorArcRelaxedLastPrimePhaseResidueSum_eq_sum_blocks
    {X J m q residue : Nat} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (theta : Real) :
    majorArcRelaxedLastPrimePhaseResidueSum X m q residue theta =
      ∑ j ∈ Finset.range J,
        majorArcPrimePhaseResidueBlockSum
          (X : Real) J m j q residue theta := by
  let P := fun p : Nat => p ≡ residue [MOD q]
  let block := fun j =>
    ((majorArcBlock (X : Real) J m j).filter P).filter Nat.Prime
  let term := fun p : Nat =>
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)
  have hpairwise :
      Set.PairwiseDisjoint (Finset.range J : Set Nat) block := by
    exact Finset.pairwiseDisjoint_filter
      (Finset.pairwiseDisjoint_filter
        (majorArcBlocks_pairwiseDisjoint
          (by exact_mod_cast hX) hJ hm) P) Nat.Prime
  have hcarrier :
      ((majorArcStrictCutoff ((X : Real) / (m : Real))).filter
          Nat.Prime).filter P =
        (Finset.range J).biUnion block := by
    rw [← majorArcBlocks_biUnion_eq_strictCutoff
      (X := (X : Real)) (J := J) (m := m)
      (by exact_mod_cast hX) hJ hm]
    ext p
    simp only [Finset.mem_filter, Finset.mem_biUnion, block, P]
    constructor
    · rintro ⟨⟨hpBlocks, hpPrime⟩, hpMod⟩
      rcases hpBlocks with ⟨j, hj, hpBlock⟩
      exact ⟨j, hj, ⟨⟨hpBlock, hpMod⟩, hpPrime⟩⟩
    · rintro ⟨j, hj, hp⟩
      rcases hp with ⟨⟨hpBlock, hpMod⟩, hpPrime⟩
      exact ⟨⟨⟨j, hj, hpBlock⟩, hpPrime⟩, hpMod⟩
  unfold majorArcRelaxedLastPrimePhaseResidueSum
  change (∑ p ∈ ((majorArcStrictCutoff
      ((X : Real) / (m : Real))).filter Nat.Prime).filter P, term p) = _
  rw [hcarrier, Finset.sum_biUnion hpairwise]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

theorem majorArcPrimePhaseResidueBlockSum_signed
    (X : Real) (J m j q residue : Nat) (b c : Int) :
    majorArcPrimePhaseResidueBlockSum X J m j q residue
        ((b : Real) / (q : Real) + (c : Real) / X) =
      majorArcSignedPrimePhaseResidueSum X J m j q residue b c :=
  rfl

/-- Signed subdivision after summing over the complete reduced residue
system. In particular, modulus one retains residue zero. -/
theorem majorArcRelaxedReduced_signed_eq_sum_blocks
    {X J m q : Nat} {b c : Int}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) (_hq : 0 < q) :
    (∑ r ∈ majorArcReducedResidues q,
      majorArcRelaxedLastPrimePhaseResidueSum X m q r
        ((b : Real) / (q : Real) + (c : Real) / (X : Real))) =
      ∑ j ∈ Finset.range J,
        ∑ r ∈ majorArcReducedResidues q,
          majorArcSignedPrimePhaseResidueSum
            (X : Real) J m j q r b c := by
  simp_rw [majorArcRelaxedLastPrimePhaseResidueSum_eq_sum_blocks
    hX hJ hm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  exact majorArcPrimePhaseResidueBlockSum_signed
    (X : Real) J m j q r b c

/-- Exact separation of the retained zero block from all positive blocks. -/
theorem majorArcRelaxedReduced_signed_eq_zero_add_positive
    {X J m q : Nat} {b c : Int}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) (hq : 0 < q) :
    (∑ r ∈ majorArcReducedResidues q,
      majorArcRelaxedLastPrimePhaseResidueSum X m q r
        ((b : Real) / (q : Real) + (c : Real) / (X : Real))) =
      (∑ r ∈ majorArcReducedResidues q,
        majorArcSignedPrimePhaseResidueSum
          (X : Real) J m 0 q r b c) +
      ∑ j ∈ Finset.Ico 1 J,
        ∑ r ∈ majorArcReducedResidues q,
          majorArcSignedPrimePhaseResidueSum
            (X : Real) J m j q r b c := by
  rw [majorArcRelaxedReduced_signed_eq_sum_blocks hX hJ hm hq]
  exact Finset.sum_range_eq_add_Ico _ hJ

private theorem norm_majorArcSignedPrimePhaseResidueSum_le_primeLog
    (X : Real) (J m j q residue : Nat) (b c : Int) :
    ‖majorArcSignedPrimePhaseResidueSum X J m j q residue b c‖ ≤
      majorArcPrimeLogResidueSum X J m j q residue := by
  unfold majorArcSignedPrimePhaseResidueSum majorArcPrimeLogResidueSum
  calc
    ‖∑ p ∈ ((majorArcBlock X J m j).filter
        (fun n => n ≡ residue [MOD q])).filter Nat.Prime,
        (Real.log (p : Real) : Complex) *
          majorArcPhase (((m * p : Nat) : Real) *
            ((b : Real) / (q : Real) + (c : Real) / X))‖ ≤
      ∑ p ∈ ((majorArcBlock X J m j).filter
          (fun n => n ≡ residue [MOD q])).filter Nat.Prime,
        ‖(Real.log (p : Real) : Complex) *
          majorArcPhase (((m * p : Nat) : Real) *
            ((b : Real) / (q : Real) + (c : Real) / X))‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ ((majorArcBlock X J m j).filter
        (fun n => n ≡ residue [MOD q])).filter Nat.Prime,
        Real.log (p : Real) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg p), majorArcPhase,
        Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem sum_majorArcBlock_reduced_primeLog_le
    {X : Real} {J m j q : Nat} (hq : 0 < q) :
    (∑ r ∈ majorArcReducedResidues q,
      majorArcPrimeLogResidueSum X J m j q r) ≤
      ∑ p ∈ (majorArcBlock X J m j).filter Nat.Prime,
        Real.log (p : Real) := by
  let primeBlock := (majorArcBlock X J m j).filter Nat.Prime
  have hall :
      (∑ r ∈ Finset.range q,
        majorArcPrimeLogResidueSum X J m j q r) =
      ∑ p ∈ primeBlock, Real.log (p : Real) := by
    have hmaps : ∀ p ∈ primeBlock, p % q ∈ Finset.range q := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.mod_lt p hq)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => Real.log (p : Real))]
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    unfold majorArcPrimeLogResidueSum
    apply Finset.sum_congr
    · ext p
      simp [primeBlock, Nat.ModEq, Nat.mod_eq_of_lt hrq,
        and_left_comm, and_comm]
    · intro p hp
      rfl
  calc
    (∑ r ∈ majorArcReducedResidues q,
        majorArcPrimeLogResidueSum X J m j q r) ≤
      ∑ r ∈ Finset.range q,
        majorArcPrimeLogResidueSum X J m j q r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro r hr hnot
      unfold majorArcPrimeLogResidueSum
      exact Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
    _ = ∑ p ∈ primeBlock, Real.log (p : Real) := hall

/-- The collective reduced zero block is bounded by the full prime-log mass
of that one block. -/
theorem norm_majorArcSignedReducedZeroBlock_le
    {X J m q : Nat} {b c : Int}
    (hJ : 0 < J) (hm : 0 < m) (hq : 0 < q) :
    ‖∑ r ∈ majorArcReducedResidues q,
      majorArcSignedPrimePhaseResidueSum
        (X : Real) J m 0 q r b c‖ ≤
      Real.log 4 * majorArcBlockLength (X : Real) J m := by
  calc
    ‖∑ r ∈ majorArcReducedResidues q,
        majorArcSignedPrimePhaseResidueSum
          (X : Real) J m 0 q r b c‖ ≤
      ∑ r ∈ majorArcReducedResidues q,
        ‖majorArcSignedPrimePhaseResidueSum
          (X : Real) J m 0 q r b c‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ majorArcReducedResidues q,
        majorArcPrimeLogResidueSum (X : Real) J m 0 q r := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_majorArcSignedPrimePhaseResidueSum_le_primeLog
        (X : Real) J m 0 q r b c
    _ ≤ ∑ p ∈ (majorArcBlock (X : Real) J m 0).filter Nat.Prime,
        Real.log (p : Real) := sum_majorArcBlock_reduced_primeLog_le hq
    _ ≤ Real.log 4 * majorArcBlockLength (X : Real) J m :=
      majorArcZeroBlock_primeLog_le hJ hm

end PrimesRestrictedDigits
