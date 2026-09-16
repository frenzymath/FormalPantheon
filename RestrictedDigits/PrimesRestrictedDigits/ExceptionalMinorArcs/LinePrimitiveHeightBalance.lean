import PrimesRestrictedDigits.ExceptionalMinorArcs.LineLargeHeightExpansion
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightCardinality
import Mathlib.Tactic.GCongr

/-!
# Balance of the primitive-height estimates

This combines the corrected forms of equations `(15.4)` and `(15.5)` to prove equation
`(15.6)` of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 212--213.
-/

open Filter

namespace PrimesRestrictedDigits

/-- The two opposing primitive-height terms balance at `H^(3/2) V^4`; the
remaining exact endpoint coefficient is absorbed only in the eventual proof. -/
theorem min_primitiveHeightTerms_le_ten_balancedTerms
    (H U V X : Real) (hH : 0 <= H) (hU : 0 < U)
    (hV : 1 <= V) (hX : 0 < X) :
    min (H * U * V ^ 5)
        (H ^ 2 * V ^ 3 / U + H ^ (3 / 2 : Real) * V ^ 4 +
          10 * (H ^ 2 * V ^ 6 / X)) <=
      10 * (H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X) := by
  let A := H * U * V ^ 5
  let B := H ^ 2 * V ^ 3 / U
  let C := H ^ (3 / 2 : Real) * V ^ 4
  let E := H ^ 2 * V ^ 6 / X
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hB : 0 <= B := by dsimp only [B]; positivity
  have hC : 0 <= C := by dsimp only [C]; positivity
  have hE : 0 <= E := by dsimp only [E]; positivity
  have hrpow : (H ^ (3 / 2 : Real)) ^ (2 : Nat) = H ^ (3 : Nat) := by
    calc
      (H ^ (3 / 2 : Real)) ^ (2 : Nat) =
          (H ^ (3 / 2 : Real)) ^ (2 : Real) :=
        (Real.rpow_natCast _ 2).symm
      _ = H ^ ((3 / 2 : Real) * 2) :=
        (Real.rpow_mul hH (3 / 2 : Real) 2).symm
      _ = H ^ (3 : Real) := by norm_num
      _ = H ^ (3 : Nat) := Real.rpow_natCast H 3
  have hproduct : A * B = C ^ 2 := by
    dsimp only [A, B, C]
    rw [mul_pow, hrpow]
    field_simp [hU.ne']
  have hminNonneg : 0 <= min A B := by positivity
  have hminSq : (min A B) ^ 2 <= C ^ 2 := by
    rw [pow_two, ← hproduct]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _)
      hminNonneg hA
  have hminAB : min A B <= C :=
    le_of_pow_le_pow_left₀ (by norm_num : (2 : Nat) ≠ 0) hC hminSq
  have hsplit :
      min A (B + C + 10 * E) <= min A B + C + 10 * E := by
    rcases le_total A B with hAB | hBA
    · rw [min_eq_left hAB]
      exact (min_le_left A (B + C + 10 * E)).trans (by nlinarith)
    · rw [min_eq_right hBA]
      exact min_le_right A (B + C + 10 * E)
  dsimp only [A, B, C, E] at hsplit hminAB hC hE ⊢
  calc
    min (H * U * V ^ 5)
        (H ^ 2 * V ^ 3 / U + H ^ (3 / 2 : Real) * V ^ 4 +
          10 * (H ^ 2 * V ^ 6 / X)) <=
      min (H * U * V ^ 5) (H ^ 2 * V ^ 3 / U) +
        H ^ (3 / 2 : Real) * V ^ 4 +
          10 * (H ^ 2 * V ^ 6 / X) := by
      convert hsplit using 1
    _ <= 2 * (H ^ (3 / 2 : Real) * V ^ 4) +
        10 * (H ^ 2 * V ^ 6 / X) := by linarith
    _ <= 10 * (H ^ (3 / 2 : Real) * V ^ 4 +
        H ^ 2 * V ^ 6 / X) := by nlinarith

/-- Uniform coefficient-one form of the balanced normalized-class estimate in
equation `(15.6)`. -/
theorem
    exists_card_orientedLineNormalizedSecondMomentClass_le_balanced_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1)))
        (j : Fin (length + 1)),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) <=
          X ^ rho *
            (H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X) := by
  obtain ⟨lengthSmall, hsmall⟩ :=
    exists_card_orientedLineNormalizedSecondMomentClass_le_small_height_threshold
      (rho / 2) (by positivity)
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
  refine ⟨max lengthSmall (max lengthLarge lengthFixed), ?_⟩
  intro length hlength C V k j hV hVX
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let F : Real := X ^ (rho / 2)
  let A : Real := H * U * V ^ 5
  let L : Real := H ^ 2 * V ^ 3 / U +
    H ^ (3 / 2 : Real) * V ^ 4 + 10 * (H ^ 2 * V ^ 6 / X)
  let T : Real := H ^ (3 / 2 : Real) * V ^ 4 + H ^ 2 * V ^ 6 / X
  let S := orientedLineNormalizedSecondMomentClass length C D V j
  have hlengthSmall : lengthSmall <= length :=
    (le_max_left _ _).trans hlength
  have hlengthLarge : lengthLarge <= length :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlength)
  have hlengthFixed : lengthFixed <= length :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlength)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hL : 0 <= L := by dsimp only [L]; positivity
  have hT : 0 <= T := by dsimp only [T]; positivity
  have hDcard : (D.card : Real) <= H := by
    dsimp only [D, H]
    exact_mod_cast lineCongruenceHeightClass_card_le_ambient length C k
  have hsmallRaw := hsmall length hlengthSmall C D V j hV hVX
  have hsmallBound : (S.card : Real) <= F * A := by
    calc
      (S.card : Real) <= F * (D.card : Real) * U * V ^ 5 := by
        simpa only [S, F, X, U] using hsmallRaw
      _ <= F * H * U * V ^ 5 := by gcongr
      _ = F * A := by dsimp only [A]; ring
  have hlargeRaw := hlarge length hlengthLarge C V k j hV hVX
  have hlargeBound : (S.card : Real) <= F * L := by
    simpa only [S, D, F, X, H, U, L] using hlargeRaw
  have hboth : (S.card : Real) <= F * min A L := by
    rw [mul_min_of_nonneg A L hF]
    exact le_min hsmallBound hlargeBound
  have hbalance : min A L <= 10 * T := by
    dsimp only [A, L, T]
    exact min_primitiveHeightTerms_le_ten_balancedTerms H U V X
      hH hU hV hX
  have hfixedAtScale : (10 : Real) <= F := by
    simpa only [F, X] using hfixed length hlengthFixed
  dsimp only [D, X, H] at ⊢
  calc
    (S.card : Real) <= F * min A L := hboth
    _ <= F * (10 * T) := mul_le_mul_of_nonneg_left hbalance hF
    _ = 10 * F * T := by ring
    _ <= F * F * T := by gcongr
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

end PrimesRestrictedDigits
