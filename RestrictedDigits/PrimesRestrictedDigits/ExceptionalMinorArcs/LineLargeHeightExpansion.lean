import PrimesRestrictedDigits.ExceptionalMinorArcs.LineLargeHeightCardinality
import Mathlib.Tactic.GCongr

/-!
# Expansion of the large primitive-height estimate

This implements the corrected passage to equation `(15.5)` of `MAYNARD-PRD-PUBLISHED`, Lemma
15.2, pp. 212--213. Exact factor-ten bins leave a factor ten on the final term before eventual
absorption.
-/

open Filter

namespace PrimesRestrictedDigits

/-- The weighted minimum used in the middle term of equation `(15.5)`. -/
theorem min_sq_pow_four_le_mul_rpow_three_halves
    (H M : Real) (hH : 0 <= H) (hM : 0 <= M) :
    min (H ^ 2) (M ^ 4) <= M * H ^ (3 / 2 : Real) := by
  let P := min (H ^ 2) (M ^ 4)
  have hP : 0 <= P := by
    dsimp only [P]
    positivity
  have hPH : P <= H ^ 2 := min_le_left _ _
  have hPM : P <= M ^ 4 := min_le_right _ _
  have htarget : 0 <= M * H ^ (3 / 2 : Real) := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : Nat) ≠ 0) htarget
  have hrpow : (H ^ (3 / 2 : Real)) ^ (4 : Nat) = H ^ (6 : Nat) := by
    calc
      (H ^ (3 / 2 : Real)) ^ (4 : Nat) =
          (H ^ (3 / 2 : Real)) ^ (4 : Real) :=
        (Real.rpow_natCast _ 4).symm
      _ = H ^ ((3 / 2 : Real) * 4) :=
        (Real.rpow_mul hH (3 / 2 : Real) 4).symm
      _ = H ^ (6 : Real) := by norm_num
      _ = H ^ (6 : Nat) := Real.rpow_natCast H 6
  calc
    P ^ 4 = P ^ 3 * P := by ring
    _ <= (H ^ 2) ^ 3 * (M ^ 4) := by gcongr
    _ = (M * H ^ (3 / 2 : Real)) ^ 4 := by
      rw [mul_pow, hrpow]
      ring

/-- A nonempty oriented bin has upper factor-ten scale strictly below `10V`. -/
theorem orientedLineNormalizedSecondMomentClass_nonempty_scale_lt
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    (hne : (orientedLineNormalizedSecondMomentClass
      length C D V j).Nonempty) :
    ((10 ^ j.val : Nat) : Real) < 10 * V := by
  let data := hne.choose
  have hdata : data ∈
      orientedLineNormalizedSecondMomentClass length C D V j :=
    hne.choose_spec
  have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
  have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
  have hscale := mem_lineNormalizedSecondMomentClass_gcd_scale_lt hfull
  have hdOne : (1 : Real) <= data.d := by
    exact_mod_cast hvalid.d_pos
  have hU : (0 : Real) <= ((10 ^ j.val : Nat) : Real) := by positivity
  calc
    ((10 ^ j.val : Nat) : Real) =
        1 * ((10 ^ j.val : Nat) : Real) := by ring
    _ <= (data.d : Real) * ((10 ^ j.val : Nat) : Real) :=
      mul_le_mul_of_nonneg_right hdOne hU
    _ < 10 * V := hscale

/-- Exact large-height expansion. The factor ten occurs only in the endpoint
term and is retained until an eventual wrapper absorbs it. -/
theorem largeHeightTerms_le_expandedTermsWithTen
    (H M U V X : Real)
    (hH : 0 <= H) (hM : 0 < M) (hU : 0 < U)
    (hV : 1 <= V) (hX : 0 < X) (hUV : U < 10 * V) :
    min (H ^ 2) (M ^ 4) *
        (V ^ 3 / U + V ^ 4 / M + U * V ^ 5 / X) <=
      H ^ 2 * V ^ 3 / U + H ^ (3 / 2 : Real) * V ^ 4 +
        10 * (H ^ 2 * V ^ 6 / X) := by
  let P := min (H ^ 2) (M ^ 4)
  have hP : 0 <= P := by
    dsimp only [P]
    positivity
  have hPH : P <= H ^ 2 := min_le_left _ _
  have hPMH : P <= M * H ^ (3 / 2 : Real) := by
    dsimp only [P]
    exact min_sq_pow_four_le_mul_rpow_three_halves H M hH hM.le
  have h1 : P * (V ^ 3 / U) <= H ^ 2 * V ^ 3 / U := by
    calc
      P * (V ^ 3 / U) <= H ^ 2 * (V ^ 3 / U) :=
        mul_le_mul_of_nonneg_right hPH (by positivity)
      _ = H ^ 2 * V ^ 3 / U := by ring
  have h2 : P * (V ^ 4 / M) <= H ^ (3 / 2 : Real) * V ^ 4 := by
    calc
      P * (V ^ 4 / M) = (P / M) * V ^ 4 := by ring
      _ <= H ^ (3 / 2 : Real) * V ^ 4 := by
        gcongr
        exact (div_le_iff₀ hM).2 (by simpa [mul_comm] using hPMH)
  have h3 : P * (U * V ^ 5 / X) <=
      10 * (H ^ 2 * V ^ 6 / X) := by
    calc
      P * (U * V ^ 5 / X) <=
          H ^ 2 * ((10 * V) * V ^ 5 / X) := by gcongr
      _ = 10 * (H ^ 2 * V ^ 6 / X) := by ring
  rw [mul_add, mul_add]
  gcongr

/-- Endpoint-corrected expanded large-height estimate, retaining the exact
factor ten before asymptotic normalization. -/
theorem
    exists_card_orientedLineNormalizedSecondMomentClass_le_expanded_large_height_with_ten_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1)))
        (j : Fin (length + 1)),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        let U : Real := ((10 ^ j.val : Nat) : Real)
        ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) <=
          X ^ rho *
            (H ^ 2 * V ^ 3 / U + H ^ (3 / 2 : Real) * V ^ 4 +
              10 * (H ^ 2 * V ^ 6 / X)) := by
  obtain ⟨lengthLarge, hlarge⟩ :=
    exists_card_orientedLineNormalizedSecondMomentClass_le_large_height_threshold
      rho hrho
  refine ⟨lengthLarge, ?_⟩
  intro length hlength C V k j hV hVX
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let M : Real := ((10 ^ k.2.val : Nat) : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let P : Real := min (H ^ 2) (M ^ 4)
  let S := orientedLineNormalizedSecondMomentClass length C D V j
  have hX : 0 < X := by dsimp only [X]; positivity
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  by_cases hS : S.Nonempty
  · have hUV : U < 10 * V := by
      dsimp only [S, U] at hS ⊢
      exact orientedLineNormalizedSecondMomentClass_nonempty_scale_lt hS
    have hterms := largeHeightTerms_le_expandedTermsWithTen
      H M U V X hH hM hU hV hX hUV
    have hraw := hlarge length hlength C V k j hV hVX
    dsimp only [D, X, H, M, U] at hraw ⊢
    calc
      ((orientedLineNormalizedSecondMomentClass length C
          (lineCongruenceHeightClass length C k) V j).card : Real) <=
        (((10 ^ length : Nat) : Real) ^ rho) *
          min ((C.card : Real) ^ 2)
            (((10 ^ k.2.val : Nat) : Real) ^ 4) *
          (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
            V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
            ((10 ^ j.val : Nat) : Real) * V ^ 5 /
              ((10 ^ length : Nat) : Real)) := hraw
      _ = (((10 ^ length : Nat) : Real) ^ rho) *
          (min ((C.card : Real) ^ 2)
            (((10 ^ k.2.val : Nat) : Real) ^ 4) *
          (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
            V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
            ((10 ^ j.val : Nat) : Real) * V ^ 5 /
              ((10 ^ length : Nat) : Real))) := by ring
      _ <= (((10 ^ length : Nat) : Real) ^ rho) *
          ((C.card : Real) ^ 2 * V ^ 3 /
              ((10 ^ j.val : Nat) : Real) +
            ((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
            10 * ((C.card : Real) ^ 2 * V ^ 6 /
              ((10 ^ length : Nat) : Real))) := by
        gcongr
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    dsimp only [D, X, H, U] at ⊢
    rw [show orientedLineNormalizedSecondMomentClass length C
        (lineCongruenceHeightClass length C k) V j = ∅ by
      simpa only [S, D] using hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Coefficient-one form of the corrected source equation `(15.5)`. -/
theorem
    exists_card_orientedLineNormalizedSecondMomentClass_le_expanded_large_height_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1)))
        (j : Fin (length + 1)),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        let U : Real := ((10 ^ j.val : Nat) : Real)
        ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) <=
          X ^ rho *
            (H ^ 2 * V ^ 3 / U + H ^ (3 / 2 : Real) * V ^ 4 +
              H ^ 2 * V ^ 6 / X) := by
  obtain ⟨lengthLarge, hlarge⟩ :=
    exists_card_orientedLineNormalizedSecondMomentClass_le_expanded_large_height_with_ten_threshold
      (rho / 2) (by positivity)
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10))
  have hgrowth : Tendsto
      (fun length : Nat => ((10 ^ length : Nat) : Real) ^ (rho / 2))
      atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < rho / 2)).comp hscale
  obtain ⟨lengthFixed, hfixed⟩ :=
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 10)
  refine ⟨max lengthLarge lengthFixed, ?_⟩
  intro length hlength C V k j hV hVX
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let E : Real := X ^ (rho / 2)
  let T : Real := H ^ 2 * V ^ 3 / U +
    H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X
  have hlengthLarge : lengthLarge <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFixed : lengthFixed <= length :=
    (le_max_right _ _).trans hlength
  have hX : 0 < X := by dsimp only [X]; positivity
  have hE : 0 <= E := by dsimp only [E]; positivity
  have hT : 0 <= T := by dsimp only [T, H, U, X]; positivity
  have hraw := hlarge length hlengthLarge C V k j hV hVX
  have hfixedAtScale : (10 : Real) <= E := by
    simpa only [E, X] using hfixed length hlengthFixed
  dsimp only [D, X, H, U] at hraw ⊢
  calc
    ((orientedLineNormalizedSecondMomentClass length C
        (lineCongruenceHeightClass length C k) V j).card : Real) <=
      (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        ((C.card : Real) ^ 2 * V ^ 3 /
            ((10 ^ j.val : Nat) : Real) +
          ((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
          10 * ((C.card : Real) ^ 2 * V ^ 6 /
            ((10 ^ length : Nat) : Real))) := hraw
    _ <= (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        (10 * ((C.card : Real) ^ 2 * V ^ 3 /
              ((10 ^ j.val : Nat) : Real) +
            ((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
            (C.card : Real) ^ 2 * V ^ 6 /
              ((10 ^ length : Nat) : Real))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : 0 <= (C.card : Real) ^ 2 * V ^ 3 /
          ((10 ^ j.val : Nat) : Real) := by positivity
      have h2 : 0 <= ((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 := by
        positivity
      have h3 : 0 <= (C.card : Real) ^ 2 * V ^ 6 /
          ((10 ^ length : Nat) : Real) := by positivity
      nlinarith
    _ = 10 * E * T := by
      dsimp only [E, T, X, H, U]
      ring
    _ <= E * E * T := by gcongr
    _ = X ^ rho * T := by
      rw [show E * E = X ^ rho by
        dsimp only [E]
        rw [← Real.rpow_add hX]
        congr 1
        ring]
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        ((C.card : Real) ^ 2 * V ^ 3 /
            ((10 ^ j.val : Nat) : Real) +
          ((C.card : Real) ^ (3 / 2 : Real)) * V ^ 4 +
          (C.card : Real) ^ 2 * V ^ 6 /
            ((10 ^ length : Nat) : Real)) := rfl

end PrimesRestrictedDigits
