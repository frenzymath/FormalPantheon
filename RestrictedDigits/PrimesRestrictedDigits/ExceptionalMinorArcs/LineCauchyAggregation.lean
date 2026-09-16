import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCauchyFibers
import PrimesRestrictedDigits.ExceptionalMinorArcs.LinePrimitiveHeightAggregation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cauchy aggregation over line congruence height classes

This sums the exact modulus/minimum classes in the Cauchy step of `MAYNARD-PRD-PUBLISHED`,
Lemma 15.2, pp. 211--214.
-/

open Filter
open Asymptotics

namespace PrimesRestrictedDigits

/-- The second-coordinate classes cover every residual pair. -/
theorem biUnion_residualLowHeightPlanePairsInClass_eq
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V : Real)
    (hV : 0 <= V) :
    (decimalFactorTenIndexPairs length).biUnion (fun k =>
        residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V) =
      residualLowHeightPlanePairs C V := by
  classical
  apply Finset.Subset.antisymm
  · intro pair hpair
    obtain ⟨k, _hk, hclass⟩ := Finset.mem_biUnion.mp hpair
    exact (mem_residualLowHeightPlanePairsInClass.mp hclass).1
  · intro pair hpair
    have hlow := mem_residualLowHeightPlanePairs.mp hpair
    have hp2C := (mem_lowHeightPlanePairs.mp hlow.1).2.1
    obtain ⟨w, hw, _hw1, hw2⟩ :=
      exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual hV hpair
    have hwCandidate := mem_positivePlaneWitnessCandidates.mp
      (mem_positiveAllNonzeroPlaneWitnesses.mp hw).1
    have hp2Pos : 0 < pair.2.val := by
      rw [← hw2]
      exact hwCandidate.2.2.2.1
    have hp2Union :
        pair.2 ∈ (decimalFactorTenIndexPairs length).biUnion
          (lineCongruenceHeightClass length C) :=
      mem_biUnion_lineCongruenceHeightClass.mpr ⟨hp2C, hp2Pos⟩
    obtain ⟨k, hk, hp2Class⟩ := Finset.mem_biUnion.mp hp2Union
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hk, mem_residualLowHeightPlanePairsInClass.mpr
      ⟨hpair, hp2Class⟩⟩

/-- Distinct modulus/minimum indices give disjoint residual-pair classes. -/
theorem pairwiseDisjoint_residualLowHeightPlanePairsInClass
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V : Real) :
    ((decimalFactorTenIndexPairs length :
      Finset (Fin (length + 1) × Fin (length + 1))) :
      Set (Fin (length + 1) × Fin (length + 1))).PairwiseDisjoint
        (fun k => residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V) := by
  intro k _hk l _hl hkl
  change Disjoint
    (residualLowHeightPlanePairsInClass C
      (lineCongruenceHeightClass length C k) V)
    (residualLowHeightPlanePairsInClass C
      (lineCongruenceHeightClass length C l) V)
  rw [Finset.disjoint_left]
  intro pair hpairK hpairL
  have hsecondK :=
    (mem_residualLowHeightPlanePairsInClass.mp hpairK).2
  have hsecondL :=
    (mem_residualLowHeightPlanePairsInClass.mp hpairL).2
  have hdisjoint := disjoint_lineCongruenceHeightClass_of_ne C hkl
  exact (Finset.disjoint_left.mp hdisjoint) hsecondK hsecondL

/-- Exact cardinality decomposition over all modulus/minimum classes. -/
theorem card_residualLowHeightPlanePairs_eq_sum_classes
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V : Real)
    (hV : 0 <= V) :
    (residualLowHeightPlanePairs C V).card =
      ∑ k ∈ decimalFactorTenIndexPairs length,
        (residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V).card := by
  classical
  calc
    (residualLowHeightPlanePairs C V).card =
        ((decimalFactorTenIndexPairs length).biUnion (fun k =>
          residualLowHeightPlanePairsInClass C
            (lineCongruenceHeightClass length C k) V)).card := by
      rw [biUnion_residualLowHeightPlanePairsInClass_eq C V hV]
    _ = ∑ k ∈ decimalFactorTenIndexPairs length,
        (residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V).card :=
      Finset.card_biUnion
        (pairwiseDisjoint_residualLowHeightPlanePairsInClass C V)

/-- A uniform per-class real bound incurs exactly `(length+1)^2`. -/
theorem card_residualLowHeightPlanePairs_real_le_index_sq_mul
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V B : Real)
    (hV : 0 <= V)
    (hclass : forall k, k ∈ decimalFactorTenIndexPairs length ->
      ((residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V).card : Real) <= B) :
    ((residualLowHeightPlanePairs C V).card : Real) <=
      (((length + 1) ^ 2 : Nat) : Real) * B := by
  have hcard := card_residualLowHeightPlanePairs_eq_sum_classes C V hV
  calc
    ((residualLowHeightPlanePairs C V).card : Real) =
        ∑ k ∈ decimalFactorTenIndexPairs length,
          ((residualLowHeightPlanePairsInClass C
            (lineCongruenceHeightClass length C k) V).card : Real) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun n : Nat => (n : Real)) hcard
    _ <= ∑ _k ∈ decimalFactorTenIndexPairs length, B :=
      Finset.sum_le_sum fun k hk => hclass k hk
    _ = ((decimalFactorTenIndexPairs length).card : Real) * B := by
      simp
    _ = (((length + 1) ^ 2 : Nat) : Real) * B := by
      rw [card_decimalFactorTenIndexPairs]

private theorem sqrt_add_le_sqrt_add_sqrt
    (A B : Real) (hA : 0 <= A) (hB : 0 <= B) :
    Real.sqrt (A + B) <= Real.sqrt A + Real.sqrt B := by
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

private theorem sqrt_mul_sourceFirstTerm
    (H V : Real) (hH : 0 <= H) (_hV : 0 <= V) :
    Real.sqrt (H * (H ^ (3 / 2 : Real) * V ^ 4)) =
      H ^ (5 / 4 : Real) * V ^ 2 := by
  calc
    Real.sqrt (H * (H ^ (3 / 2 : Real) * V ^ 4)) =
        Real.sqrt H * Real.sqrt (H ^ (3 / 2 : Real) * V ^ 4) :=
      Real.sqrt_mul hH _
    _ = Real.sqrt H *
        (Real.sqrt (H ^ (3 / 2 : Real)) * Real.sqrt (V ^ 4)) := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hH _)]
    _ = H ^ (1 / 2 : Real) *
        ((H ^ (3 / 2 : Real)) ^ (1 / 2 : Real) * V ^ 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      congr 2
      rw [show V ^ 4 = (V ^ 2) ^ 2 by ring,
        Real.sqrt_sq (sq_nonneg V)]
    _ = H ^ (1 / 2 : Real) *
        (H ^ (3 / 4 : Real) * V ^ 2) := by
      rw [← Real.rpow_mul hH]
      congr 3
      norm_num
    _ = H ^ (5 / 4 : Real) * V ^ 2 := by
      rw [← mul_assoc,
        ← Real.rpow_add_of_nonneg hH (by norm_num) (by norm_num)]
      congr 2
      norm_num

private theorem sqrt_mul_sourceSecondTerm
    (H V X : Real) (hH : 0 <= H) (hV : 0 <= V) (_hX : 0 < X) :
    Real.sqrt (H * (H ^ 2 * V ^ 6 / X)) =
      H ^ (3 / 2 : Real) * V ^ 3 / X ^ (1 / 2 : Real) := by
  calc
    Real.sqrt (H * (H ^ 2 * V ^ 6 / X)) =
        Real.sqrt (H * (H ^ 2 * V ^ 6)) / Real.sqrt X := by
      rw [show H * (H ^ 2 * V ^ 6 / X) =
        (H * (H ^ 2 * V ^ 6)) / X by ring]
      exact Real.sqrt_div (by positivity) X
    _ = Real.sqrt (H * (H ^ 2 * V ^ 6)) /
        X ^ (1 / 2 : Real) := by
      rw [Real.sqrt_eq_rpow X]
    _ = (H ^ (3 / 2 : Real) * V ^ 3) /
        X ^ (1 / 2 : Real) := by
      congr 1
      rw [show H * (H ^ 2 * V ^ 6) =
        H ^ 3 * (V ^ 3) ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
        ← Real.rpow_natCast]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hH]
      congr 2
      norm_num
    _ = H ^ (3 / 2 : Real) * V ^ 3 /
        X ^ (1 / 2 : Real) := rfl

private theorem sqrt_rpow_eq_rpow_half
    (X rho : Real) (hX : 0 < X) :
    Real.sqrt (X ^ rho) = X ^ (rho / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]
  congr 1
  ring

/-- Cauchy transforms the fixed-class second-moment shape into the two
source terms, halving its subpolynomial exponent. -/
theorem card_residualLowHeightPlanePairsInClass_real_le_sourceShape
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V rho : Real)
    (k : Fin (length + 1) × Fin (length + 1)) (hV : 0 <= V)
    (htriple :
      ((residualLineSecondMomentTriples C
        (lineCongruenceHeightClass length C k) V).card : Real) <=
        (((10 ^ length : Nat) : Real) ^ rho) *
          (((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
            (C.card : Real) ^ 2 * V ^ 6 /
              ((10 ^ length : Nat) : Real))) :
    ((residualLowHeightPlanePairsInClass C
      (lineCongruenceHeightClass length C k) V).card : Real) <=
      (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        (((C.card : Real) ^ (5 / 4 : Real)) * V ^ 2 +
          (C.card : Real) ^ (3 / 2 : Real) * V ^ 3 /
            (((10 ^ length : Nat) : Real) ^ (1 / 2 : Real))) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let A : Real := H ^ (3 / 2 : Real) * V ^ 4
  let B : Real := H ^ 2 * V ^ 6 / X
  let S : Real := H ^ (5 / 4 : Real) * V ^ 2 +
    H ^ (3 / 2 : Real) * V ^ 3 / X ^ (1 / 2 : Real)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hB : 0 <= B := by dsimp only [B, X]; positivity
  have hS : 0 <= S := by dsimp only [S, H, X]; positivity
  have hcauchy :=
    card_residualLowHeightPlanePairsInClass_real_le_sqrt_mul_sqrt
      C (lineCongruenceHeightClass length C k) V
  have hsqrtTriple :
      Real.sqrt
          ((residualLineSecondMomentTriples C
            (lineCongruenceHeightClass length C k) V).card : Real) <=
        Real.sqrt (X ^ rho * (A + B)) := by
    apply Real.sqrt_le_sqrt
    simpa only [X, H, A, B] using htriple
  have hshape :
      Real.sqrt H * Real.sqrt (X ^ rho * (A + B)) <=
        X ^ (rho / 2) * S := by
    calc
      Real.sqrt H * Real.sqrt (X ^ rho * (A + B)) =
          Real.sqrt (H * (X ^ rho * (A + B))) :=
        (Real.sqrt_mul hH _).symm
      _ = Real.sqrt (X ^ rho * (H * A + H * B)) := by
        congr 1
        ring
      _ = Real.sqrt (X ^ rho) * Real.sqrt (H * A + H * B) :=
        Real.sqrt_mul (Real.rpow_nonneg hX.le rho) _
      _ <= Real.sqrt (X ^ rho) *
          (Real.sqrt (H * A) + Real.sqrt (H * B)) := by
        gcongr
        exact sqrt_add_le_sqrt_add_sqrt (H * A) (H * B)
          (mul_nonneg hH hA) (mul_nonneg hH hB)
      _ = X ^ (rho / 2) * S := by
        rw [sqrt_rpow_eq_rpow_half X rho hX]
        dsimp only [A, B, S]
        rw [sqrt_mul_sourceFirstTerm H V hH hV,
          sqrt_mul_sourceSecondTerm H V X hH hV hX]
  dsimp only [X, H, S] at hshape ⊢
  exact hcauchy.trans
    ((mul_le_mul_of_nonneg_left hsqrtTriple (Real.sqrt_nonneg _)).trans
      hshape)

/-- Coefficient-one residual-pair estimate after exact Cauchy and summing
all modulus/minimum classes. -/
theorem
    exists_card_residualLowHeightPlanePairs_le_cauchyAggregation_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((residualLowHeightPlanePairs C V).card : Real) <=
          X ^ rho *
            (H ^ (5 / 4 : Real) * V ^ 2 +
              H ^ (3 / 2 : Real) * V ^ 3 /
                X ^ (1 / 2 : Real)) := by
  obtain ⟨lengthTriples, htriples⟩ :=
    exists_card_residualLineSecondMomentTriples_le_primitiveHeight_sum_threshold
      rho hrho
  have hbase : (1 : Real) < (10 : Real) ^ (rho / 2) := by
    exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hbasePos : (0 : Real) < (10 : Real) ^ (rho / 2) := by positivity
  have hquadratic : ∀ᶠ length : Nat in atTop,
      (length : Real) ^ 2 <= (1 / 4 : Real) *
        (((10 : Real) ^ (rho / 2)) ^ length) := by
    have hlittle : (fun length : Nat => (length : Real) ^ 2) =o[atTop]
        fun length => ((10 : Real) ^ (rho / 2)) ^ length :=
      isLittleO_pow_const_const_pow_of_one_lt (R := Real) 2 hbase
    have hbound := hlittle.bound (by norm_num : (0 : Real) < 1 / 4)
    filter_upwards [hbound] with length hlength
    simpa [Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (sq_nonneg (length : Real)),
      abs_of_pos hbasePos] using hlength
  have hfactor : ∀ᶠ length : Nat in atTop,
      (((length + 1) ^ 2 : Nat) : Real) <=
        (((10 ^ length : Nat) : Real) ^ (rho / 2)) := by
    filter_upwards [hquadratic, eventually_ge_atTop 1] with length hquad hlength
    have hfirstNat : (length + 1) ^ 2 <= 4 * length ^ 2 := by
      have hlinear : length + 1 <= 2 * length := by omega
      nlinarith
    have hfirst : (((length + 1) ^ 2 : Nat) : Real) <=
        4 * (length : Real) ^ 2 := by
      exact_mod_cast hfirstNat
    have hsecond : 4 * (length : Real) ^ 2 <=
        ((10 : Real) ^ (rho / 2)) ^ length := by
      nlinarith
    calc
      (((length + 1) ^ 2 : Nat) : Real) <=
          4 * (length : Real) ^ 2 := hfirst
      _ <= ((10 : Real) ^ (rho / 2)) ^ length := hsecond
      _ = (((10 ^ length : Nat) : Real) ^ (rho / 2)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        calc
          ((10 : Real) ^ (rho / 2)) ^ length =
              (10 : Real) ^ ((rho / 2) * (length : Real)) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num) _ _).symm
          _ = (10 : Real) ^ ((length : Real) * (rho / 2)) := by
            congr 1
            ring
          _ = ((10 : Real) ^ length) ^ (rho / 2) := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_mul (by norm_num) _ _
  obtain ⟨lengthFactor, hfactor⟩ := eventually_atTop.mp hfactor
  refine ⟨max lengthTriples lengthFactor, ?_⟩
  intro length hlength C V hV hVX
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let S : Real := H ^ (5 / 4 : Real) * V ^ 2 +
    H ^ (3 / 2 : Real) * V ^ 3 / X ^ (1 / 2 : Real)
  have hlengthTriples : lengthTriples <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFactor : lengthFactor <= length :=
    (le_max_right _ _).trans hlength
  have hX : 0 < X := by dsimp only [X]; positivity
  have hS : 0 <= S := by dsimp only [S, H, X]; positivity
  have hclass : forall k, k ∈ decimalFactorTenIndexPairs length ->
      ((residualLowHeightPlanePairsInClass C
          (lineCongruenceHeightClass length C k) V).card : Real) <=
        X ^ (rho / 2) * S := by
    intro k _hk
    apply card_residualLowHeightPlanePairsInClass_real_le_sourceShape
      C V rho k (by linarith)
    simpa only [X, H] using
      htriples length hlengthTriples C V k hV hVX
  have hsum : ((residualLowHeightPlanePairs C V).card : Real) <=
      (((length + 1) ^ 2 : Nat) : Real) *
        (X ^ (rho / 2) * S) :=
    card_residualLowHeightPlanePairs_real_le_index_sq_mul
      C V (X ^ (rho / 2) * S) (by linarith) hclass
  have hfactorAtLength : (((length + 1) ^ 2 : Nat) : Real) <=
      X ^ (rho / 2) := by
    simpa only [X] using hfactor length hlengthFactor
  dsimp only [X, H, S] at hsum hfactorAtLength hS hX ⊢
  calc
    ((residualLowHeightPlanePairs C V).card : Real) <=
        (((length + 1) ^ 2 : Nat) : Real) *
          ((((10 ^ length : Nat) : Real) ^ (rho / 2)) *
            ((C.card : Real) ^ (5 / 4 : Real) * V ^ 2 +
              (C.card : Real) ^ (3 / 2 : Real) * V ^ 3 /
                ((10 ^ length : Nat) : Real) ^ (1 / 2 : Real))) := hsum
    _ <= (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
          ((((10 ^ length : Nat) : Real) ^ (rho / 2)) *
            ((C.card : Real) ^ (5 / 4 : Real) * V ^ 2 +
              (C.card : Real) ^ (3 / 2 : Real) * V ^ 3 /
                ((10 ^ length : Nat) : Real) ^ (1 / 2 : Real))) := by
      gcongr
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        ((C.card : Real) ^ (5 / 4 : Real) * V ^ 2 +
          (C.card : Real) ^ (3 / 2 : Real) * V ^ 3 /
            ((10 ^ length : Nat) : Real) ^ (1 / 2 : Real)) := by
      rw [← mul_assoc, ← Real.rpow_add hX]
      congr 2
      ring

end PrimesRestrictedDigits
