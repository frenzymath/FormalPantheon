import PrimesRestrictedDigits.MajorArcs.M2Phase
import Mathlib.NumberTheory.Chebyshev

/-!
# M2 aggregation over reduced positive blocks

This formalizes the finite reduced-residue mass and roots-of-unity
cancellation in the M2 calculation on published pp. 187--188. It assumes,
but does not prove, the scalar prime-log progression error on each block.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The reduced residue fibers over all positive blocks have at most the full
Chebyshev prime-log mass below `X / m`. -/
theorem sum_majorArcPositiveBlock_reduced_primeLog_le
    {X : Real} {J m q : Nat}
    (hX : 0 < X) (hJ : 1 < J) (hm : 0 < m) (hq : 0 < q) :
    (∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPrimeLogResidueSum X J m j q r) ≤
      Real.log 4 * (X / (m : Real)) := by
  let primeBlock := fun j =>
    (majorArcBlock X J m j).filter Nat.Prime
  have hJpos : 0 < J := Nat.zero_lt_of_lt hJ
  have hblock (j : Nat) :
      (∑ r ∈ majorArcReducedResidues q,
          majorArcPrimeLogResidueSum X J m j q r) ≤
        ∑ p ∈ primeBlock j, Real.log (p : Real) := by
    have hall :
        (∑ r ∈ Finset.range q,
            majorArcPrimeLogResidueSum X J m j q r) =
          ∑ p ∈ primeBlock j, Real.log (p : Real) := by
      have hmaps : ∀ p ∈ primeBlock j, p % q ∈ Finset.range q := by
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
        intro r hrange hrnot
        unfold majorArcPrimeLogResidueSum
        exact Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
      _ = ∑ p ∈ primeBlock j, Real.log (p : Real) := hall
  have hpositiveSubset : Finset.Ico 1 J ⊆ Finset.range J := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have hpairwise :
      Set.PairwiseDisjoint (Finset.range J : Set Nat) primeBlock := by
    exact Finset.pairwiseDisjoint_filter
      (majorArcBlocks_pairwiseDisjoint hX hJpos hm) Nat.Prime
  have hcutoff :
      (Finset.range J).biUnion primeBlock =
        (majorArcStrictCutoff (X / (m : Real))).filter Nat.Prime := by
    dsimp [primeBlock]
    rw [← Finset.filter_biUnion,
      majorArcBlocks_biUnion_eq_strictCutoff hX hJpos hm]
  have htheta :
      (∑ p ∈ (majorArcStrictCutoff (X / (m : Real))).filter Nat.Prime,
          Real.log (p : Real)) ≤
        Chebyshev.theta (X / (m : Real)) := by
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpCutoff, hpPrime⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨hpPrime.pos, ?_⟩, hpPrime⟩
      exact Nat.le_floor (mem_majorArcStrictCutoff.mp hpCutoff).le
    · intro p hpTarget hpNotSource
      exact Real.log_natCast_nonneg p
  calc
    (∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPrimeLogResidueSum X J m j q r) ≤
        ∑ j ∈ Finset.Ico 1 J,
          ∑ p ∈ primeBlock j, Real.log (p : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hblock j
    _ ≤ ∑ j ∈ Finset.range J,
        ∑ p ∈ primeBlock j, Real.log (p : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hpositiveSubset
      intro j hjRange hjNotPositive
      exact Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
    _ = ∑ p ∈ (Finset.range J).biUnion primeBlock,
        Real.log (p : Real) := (Finset.sum_biUnion hpairwise).symm
    _ = ∑ p ∈ (majorArcStrictCutoff (X / (m : Real))).filter Nat.Prime,
        Real.log (p : Real) := by rw [hcutoff]
    _ ≤ Chebyshev.theta (X / (m : Real)) := htheta
    _ ≤ Real.log 4 * (X / (m : Real)) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)

/-- Uniform scalar errors on the reduced positive blocks, together with exact
phase cancellation, give the finite M2 block bound. -/
theorem norm_sum_majorArcSignedReducedPositiveBlocks_le
    {X K : Real} {J m q : Nat} {b c : Int}
    (hX : 0 < X) (hJ : 1 < J) (hm : 0 < m) (hq : 0 < q)
    (hK : 0 ≤ K) (hc0 : c ≠ 0) (hcJ : c.natAbs < J)
    (herror : ∀ j ∈ Finset.Ico 1 J,
      ∀ r ∈ majorArcReducedResidues q,
        |majorArcPrimeLogResidueSum X J m j q r -
          majorArcPositiveBlockMainTerm X J m q| ≤
            K * majorArcPositiveBlockErrorScale X J m q) :
    ‖∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q,
        majorArcSignedPrimePhaseResidueSum X J m j q r b c‖ ≤
      (K + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4) *
        majorArcBlockLength X J m := by
  let rationalPhase := fun (r : Nat) => majorArcPhase
    ((b : Real) * (r : Real) * (m : Real) / (q : Real))
  let blockPhase := fun (j : Nat) => majorArcPhase
    ((j : Real) * majorArcSubdivisionWidth J * (c : Real))
  let A := fun (j r : Nat) => majorArcPrimeLogResidueSum X J m j q r
  let M := majorArcPositiveBlockMainTerm X J m q
  let P := fun (j r : Nat) =>
    majorArcSignedPrimePhaseResidueSum X J m j q r b c
  let main := fun (j r : Nat) =>
    rationalPhase r * blockPhase j * (M : Complex)
  let localError := fun (j r : Nat) => P j r - main j r
  let E := 2 * Real.pi * |(c : Real)| * majorArcSubdivisionWidth J
  let totalA := ∑ j ∈ Finset.Ico 1 J,
    ∑ r ∈ majorArcReducedResidues q, A j r
  let totalScalarError := ∑ j ∈ Finset.Ico 1 J,
    ∑ r ∈ majorArcReducedResidues q, |A j r - M|
  have hJpos : 0 < J := Nat.zero_lt_of_lt hJ
  have hlength : 0 ≤ majorArcBlockLength X J m := by
    rw [majorArcBlockLength]
    positivity
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hM : 0 ≤ M := by
    dsimp [M, majorArcPositiveBlockMainTerm]
    exact div_nonneg hlength (by positivity)
  have hlocal (j r : Nat) :
      ‖localError j r‖ ≤ E * A j r + |A j r - M| := by
    exact norm_majorArcSignedPrimePhaseResidueSum_sub_main_le
      (b := b) (c := c) hX hJpos hm hq
  have hdecompose :
      (∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, P j r) =
        (∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r) +
        ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r := by
    dsimp [localError]
    simp_rw [Finset.sum_sub_distrib]
    ring
  have hcancel :
      (∑ j ∈ Finset.Ico 1 J, blockPhase j) = -1 := by
    dsimp [blockPhase]
    convert majorArcPhase_sum_Ico_one_eq_neg_one_of_abs_lt hJ hc0 hcJ using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [majorArcSubdivisionWidth, inv_eq_one_div]
    ring
  have hmainRewrite :
      (∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r) =
        ∑ r ∈ majorArcReducedResidues q,
          rationalPhase r * (-1) * (M : Complex) := by
    calc
      (∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r) =
          ∑ r ∈ majorArcReducedResidues q,
            ∑ j ∈ Finset.Ico 1 J, main j r := by
        rw [Finset.sum_comm]
      _ = ∑ r ∈ majorArcReducedResidues q,
          rationalPhase r *
            (∑ j ∈ Finset.Ico 1 J, blockPhase j) * (M : Complex) := by
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [main]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = ∑ r ∈ majorArcReducedResidues q,
          rationalPhase r * (-1) * (M : Complex) := by rw [hcancel]
  have hmain :
      ‖∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r‖ ≤
        majorArcBlockLength X J m := by
    rw [hmainRewrite]
    calc
      ‖∑ r ∈ majorArcReducedResidues q,
          rationalPhase r * (-1) * (M : Complex)‖ ≤
          ∑ r ∈ majorArcReducedResidues q,
            ‖rationalPhase r * (-1) * (M : Complex)‖ :=
        norm_sum_le _ _
      _ = ∑ _r ∈ majorArcReducedResidues q, M := by
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [rationalPhase]
        rw [norm_mul, norm_mul, majorArcPhase,
          Complex.norm_exp_ofReal_mul_I, norm_neg, norm_one, mul_one,
          Complex.norm_real, Real.norm_of_nonneg hM]
        ring
      _ = (Nat.totient q : Real) * M := by
        simp [Finset.sum_const, nsmul_eq_mul,
          card_majorArcReducedResidues]
      _ = majorArcBlockLength X J m := by
        dsimp [M, majorArcPositiveBlockMainTerm]
        have hphiReal : (Nat.totient q : Real) ≠ 0 := by
          exact_mod_cast hphi.ne'
        field_simp
  have hmass : totalA ≤ Real.log 4 * (X / (m : Real)) := by
    exact sum_majorArcPositiveBlock_reduced_primeLog_le hX hJ hm hq
  have hscalar : totalScalarError ≤ K * majorArcBlockLength X J m := by
    apply sum_majorArcPositiveBlock_errors_le hX.le hK hJ hm hq
    intro j hj r hr
    exact herror j hj r hr
  have hE : 0 ≤ E := by
    dsimp [E, majorArcSubdivisionWidth]
    positivity
  have herrors :
      ‖∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r‖ ≤
        (K + 2 * Real.pi * |(c : Real)| * Real.log 4) *
          majorArcBlockLength X J m := by
    calc
      ‖∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r‖ ≤
          ∑ j ∈ Finset.Ico 1 J,
            ‖∑ r ∈ majorArcReducedResidues q, localError j r‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, ‖localError j r‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q,
            (E * A j r + |A j r - M|) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro r hr
        exact hlocal j r
      _ = E * totalA + totalScalarError := by
        dsimp [totalA, totalScalarError]
        simp_rw [Finset.sum_add_distrib]
        congr 1
        calc
          (∑ j ∈ Finset.Ico 1 J,
              ∑ r ∈ majorArcReducedResidues q, E * A j r) =
              ∑ j ∈ Finset.Ico 1 J,
                E * (∑ r ∈ majorArcReducedResidues q, A j r) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.mul_sum]
          _ = E * (∑ j ∈ Finset.Ico 1 J,
              ∑ r ∈ majorArcReducedResidues q, A j r) := by
            rw [← Finset.mul_sum]
      _ ≤ E * (Real.log 4 * (X / (m : Real))) +
          K * majorArcBlockLength X J m :=
        add_le_add (mul_le_mul_of_nonneg_left hmass hE) hscalar
      _ = (K + 2 * Real.pi * |(c : Real)| * Real.log 4) *
          majorArcBlockLength X J m := by
        rw [majorArcBlockLength_eq_width_mul X hJpos hm]
        dsimp [E]
        ring
  rw [show (∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q, P j r) =
        (∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r) +
        ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r from hdecompose]
  calc
    ‖(∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r) +
        ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r‖ ≤
        ‖∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, localError j r‖ +
        ‖∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q, main j r‖ := norm_add_le _ _
    _ ≤ (K + 2 * Real.pi * |(c : Real)| * Real.log 4) *
          majorArcBlockLength X J m + majorArcBlockLength X J m :=
      add_le_add herrors hmain
    _ = (K + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4) *
        majorArcBlockLength X J m := by ring

end PrimesRestrictedDigits
