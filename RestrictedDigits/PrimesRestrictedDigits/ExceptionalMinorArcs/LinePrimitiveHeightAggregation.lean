import PrimesRestrictedDigits.ExceptionalMinorArcs.LinePrimitiveHeightBalance
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Primitive-height aggregation for the line second moment

This implements the exact primitive-height sum between equations `(15.6)` and `(15.2)` of
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 213--214.
-/

open Filter
open Asymptotics

namespace PrimesRestrictedDigits

/-- A uniform bound for every oriented primitive-height bin gives the exact
factor `2 * (length + 1)` witness-pair bound. -/
theorem card_lineSecondMomentWitnessPairs_real_le_two_mul_succ_mul
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V B : Real)
    (hVX : V < ((10 ^ length : Nat) : Real))
    (hbin : forall j : Fin (length + 1),
      ((orientedLineNormalizedSecondMomentClass
        length C D V j).card : Real) <= B) :
    ((lineSecondMomentWitnessPairs C D V).card : Real) <=
      2 * ((length + 1 : Nat) : Real) * B := by
  have hsum :=
    card_lineSecondMomentWitnessPairs_le_sum_two_mul_oriented C D V hVX
  calc
    ((lineSecondMomentWitnessPairs C D V).card : Real) <=
        ∑ j : Fin (length + 1),
          2 * ((orientedLineNormalizedSecondMomentClass
            length C D V j).card : Real) := by
      exact_mod_cast hsum
    _ <= ∑ _j : Fin (length + 1), 2 * B := by
      apply Finset.sum_le_sum
      intro j _hj
      gcongr
      exact hbin j
    _ = 2 * ((length + 1 : Nat) : Real) * B := by
      simp
      ring

/-- Uniform coefficient-one witness-pair estimate after summing every exact
primitive-height bin while retaining a fixed modulus/minimum class. -/
theorem
    exists_card_lineSecondMomentWitnessPairs_le_primitiveHeight_sum_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1))),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((lineSecondMomentWitnessPairs C D V).card : Real) <=
          X ^ rho *
            (H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X) := by
  obtain ⟨lengthBalanced, hbalanced⟩ :=
    exists_card_orientedLineNormalizedSecondMomentClass_le_balanced_threshold
      (rho / 2) (by positivity)
  have hbase : (1 : Real) < (10 : Real) ^ (rho / 2) := by
    exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hbasePos : (0 : Real) < (10 : Real) ^ (rho / 2) := by positivity
  have hlinear : ∀ᶠ length : Nat in atTop,
      ((length : Real)) <= (1 / 4 : Real) *
        ((10 : Real) ^ (rho / 2)) ^ length := by
    have hlittle : ((↑) : Nat -> Real) =o[atTop]
        fun length => ((10 : Real) ^ (rho / 2)) ^ length :=
      isLittleO_coe_const_pow_of_one_lt hbase
    have hbound := hlittle.bound (by norm_num : (0 : Real) < 1 / 4)
    filter_upwards [hbound] with length hlength
    simpa [Real.norm_eq_abs, abs_of_nonneg, abs_of_pos hbasePos] using hlength
  have hfactor : ∀ᶠ length : Nat in atTop,
      ((2 * (length + 1) : Nat) : Real) <=
        (((10 ^ length : Nat) : Real) ^ (rho / 2)) := by
    filter_upwards [hlinear, eventually_ge_atTop 1] with length hlinear hlength
    have hfirst : ((2 * (length + 1) : Nat) : Real) <=
        4 * (length : Real) := by
      exact_mod_cast (show 2 * (length + 1) <= 4 * length by omega)
    have hsecond : 4 * (length : Real) <=
        ((10 : Real) ^ (rho / 2)) ^ length := by
      nlinarith
    calc
      ((2 * (length + 1) : Nat) : Real) <=
          4 * (length : Real) := hfirst
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
  refine ⟨max lengthBalanced lengthFactor, ?_⟩
  intro length hlength C V k hV hVX
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let F : Real := X ^ (rho / 2)
  let T : Real := H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X
  have hlengthBalanced : lengthBalanced <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFactor : lengthFactor <= length :=
    (le_max_right _ _).trans hlength
  have hX : 0 < X := by dsimp only [X]; positivity
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hT : 0 <= T := by dsimp only [T, H, X]; positivity
  have hbin : forall j : Fin (length + 1),
      ((orientedLineNormalizedSecondMomentClass
        length C D V j).card : Real) <= F * T := by
    intro j
    have hraw := hbalanced length hlengthBalanced C V k j hV hVX
    simpa only [D, F, T, X, H] using hraw
  have hwitness : ((lineSecondMomentWitnessPairs C D V).card : Real) <=
      ((2 * (length + 1) : Nat) : Real) * (F * T) := by
    convert card_lineSecondMomentWitnessPairs_real_le_two_mul_succ_mul
      C D V (F * T) hVX hbin using 1; norm_num
  have hfactorAtLength : ((2 * (length + 1) : Nat) : Real) <= F := by
    simpa only [F, X] using hfactor length hlengthFactor
  dsimp only [D, X, H] at ⊢
  calc
    ((lineSecondMomentWitnessPairs C
        (lineCongruenceHeightClass length C k) V).card : Real) <=
      ((2 * (length + 1) : Nat) : Real) * (F * T) := hwitness
    _ <= F * (F * T) := by gcongr
    _ = (F * F) * T := by ring
    _ = X ^ rho * T := by
      rw [show F * F = X ^ rho by
        dsimp only [F]
        rw [← Real.rpow_add hX]
        congr 1
        ring]
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        (((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
          (C.card : Real) ^ 2 * V ^ 6 /
            ((10 ^ length : Nat) : Real)) := rfl

/-- Source-facing corrected `N_2` bound after primitive-height aggregation. -/
theorem exists_card_lineSecondMomentTriples_le_primitiveHeight_sum_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1))),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((lineSecondMomentTriples C D V).card : Real) <=
          X ^ rho *
            (H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X) := by
  obtain ⟨length0, hlength⟩ :=
    exists_card_lineSecondMomentWitnessPairs_le_primitiveHeight_sum_threshold
      rho hrho
  refine ⟨length0, ?_⟩
  intro length hlength0 C V k hV hVX
  let D := lineCongruenceHeightClass length C k
  have hDC : D ⊆ C := by
    intro a ha
    exact (mem_lineCongruenceHeightClass.mp ha).1
  have hcard :
      ((lineSecondMomentTriples C D V).card : Real) <=
        ((lineSecondMomentWitnessPairs C D V).card : Real) := by
    exact_mod_cast card_lineSecondMomentTriples_le_witnessPairs
      ((by norm_num : (0 : Real) <= 1).trans hV) hDC
  exact hcard.trans (hlength length hlength0 C V k hV hVX)

/-- Residual second-moment bound after removing the disjoint zero-term cover
and summing the primitive-height bins. -/
theorem
    exists_card_residualLineSecondMomentTriples_le_primitiveHeight_sum_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1))),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((residualLineSecondMomentTriples C D V).card : Real) <=
          X ^ rho *
            (H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X) := by
  obtain ⟨length0, hlength⟩ :=
    exists_card_lineSecondMomentWitnessPairs_le_primitiveHeight_sum_threshold
      rho hrho
  refine ⟨length0, ?_⟩
  intro length hlength0 C V k hV hVX
  let D := lineCongruenceHeightClass length C k
  have hcard :
      ((residualLineSecondMomentTriples C D V).card : Real) <=
        ((lineSecondMomentWitnessPairs C D V).card : Real) := by
    exact_mod_cast card_residualLineSecondMomentTriples_le_witnessPairs
      ((by norm_num : (0 : Real) <= 1).trans hV)
  exact hcard.trans (hlength length hlength0 C V k hV hVX)

end PrimesRestrictedDigits
