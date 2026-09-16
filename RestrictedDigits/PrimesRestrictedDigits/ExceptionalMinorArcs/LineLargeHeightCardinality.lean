import PrimesRestrictedDigits.BasicEstimates.DecimalDivisorBound
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceHeightClassCardinality
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineLargeHeightAffineFiber
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightLinearFibers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr

/-!
# Cardinality of the large primitive-height normalized class

This composes the corrected affine cross fiber with the existing three divisor and two
coprime-linear suffix fibers. It proves the large-height estimate immediately before equation
`(15.5)` of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 212--213.
-/

open Filter

namespace PrimesRestrictedDigits

/-- Explicit finite form of the large primitive-height count. -/
theorem orientedLineNormalizedSecondMomentClass_card_real_le_large_height
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V Q : Real)
    (k : Prod (Fin (length + 1)) (Fin (length + 1)))
    (j : Fin (length + 1))
    (hV : 1 ≤ V) (hVX : V < ((10 ^ length : Nat) : Real))
    (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤
          6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    let D := lineCongruenceHeightClass length C k
    let X : Real := ((10 ^ length : Nat) : Real)
    let M : Real := ((10 ^ k.2.val : Nat) : Real)
    let U : Real := ((10 ^ j.val : Nat) : Real)
    ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) ≤
      6144000 * (D.card : Real) ^ 2 * Q ^ 3 *
        (V ^ 3 / U + 6 * V ^ 4 / M + 36 * U * V ^ 5 / X) := by
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let M : Real := ((10 ^ k.2.val : Nat) : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let B : Real := 6 * U * V
  let R : Real := 40 * V / U
  have hX : 0 < X := by dsimp only [X]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hF : 0 ≤ 640 * (1 + B / M + B ^ 2 / X) := by
    have hB : 0 ≤ B := by dsimp only [B, U]; positivity
    positivity
  have h0 := lineLargeHeightKeyClass_card_real_le C D V j hV
  have h1 := lineLargeHeightCrossFactorClass_card_real_le C V k j hV
  have h2 := lineSmallHeightFirstPrimitiveFactorClass_card_real_le
    C D V Q j hV hVX hQ hfactor
  have h3 := lineSmallHeightSecondPrimitiveFactorClass_card_real_le
    C D V Q j hV hVX hQ hfactor
  have h4 := lineSmallHeightThirdPairClass_card_real_le C D V j hV
  have h5 := lineSmallHeightFourthPairClass_card_real_le C D V j hV
  have h6 := lineSmallHeightCodeClass_card_real_le
    C D V Q j hV hVX hQ hfactor
  have hcode :
      ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
        (D.card : Real) ^ 2 * (6 * U * V) *
          (640 * (1 + B / M + B ^ 2 / X)) * Q ^ 3 * R ^ 2 := by
    calc
      ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
          ((lineSmallHeightFourthPairClass length C D V j).card : Real) * Q :=
        h6
      _ ≤ (((lineSmallHeightThirdPairClass length C D V j).card : Real) *
          R) * Q := by gcongr
      _ ≤ ((((lineSmallHeightSecondPrimitiveFactorClass
          length C D V j).card : Real) * R) * R) * Q := by gcongr
      _ ≤ (((((lineSmallHeightFirstPrimitiveFactorClass
          length C D V j).card : Real) * Q) * R) * R) * Q := by gcongr
      _ ≤ ((((((lineSmallHeightCrossFactorClass
          length C D V j).card : Real) * Q) * Q) * R) * R) * Q := by gcongr
      _ ≤ ((((((lineLargeHeightKeyClass length C D V j).card : Real) *
          (640 * (1 + B / M + B ^ 2 / X)) * Q) * Q) * R) * R) * Q := by
        gcongr
      _ ≤ ((((((D.card : Real) ^ 2 * (6 * U * V)) *
          (640 * (1 + B / M + B ^ 2 / X)) * Q) * Q) * R) * R) * Q := by
        gcongr
      _ = (D.card : Real) ^ 2 * (6 * U * V) *
          (640 * (1 + B / M + B ^ 2 / X)) * Q ^ 3 * R ^ 2 := by ring
  have hcard :
      ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) =
        ((lineSmallHeightCodeClass length C D V j).card : Real) := by
    exact_mod_cast (card_lineSmallHeightCodeClass C D V j).symm
  dsimp only at ⊢
  rw [hcard]
  calc
    ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
        (D.card : Real) ^ 2 * (6 * U * V) *
          (640 * (1 + B / M + B ^ 2 / X)) * Q ^ 3 * R ^ 2 := hcode
    _ = 6144000 * (D.card : Real) ^ 2 * Q ^ 3 *
        (V ^ 3 / U + 6 * V ^ 4 / M + 36 * U * V ^ 5 / X) := by
      dsimp only [B, R]
      field_simp
      ring

/-- Uniform coefficient-one form of the large primitive-height estimate. -/
theorem exists_card_orientedLineNormalizedSecondMomentClass_le_large_height_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 ≤ length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real)
        (k : Prod (Fin (length + 1)) (Fin (length + 1)))
        (j : Fin (length + 1)),
        1 ≤ V -> V < ((10 ^ length : Nat) : Real) ->
        let D := lineCongruenceHeightClass length C k
        let X : Real := ((10 ^ length : Nat) : Real)
        let M : Real := ((10 ^ k.2.val : Nat) : Real)
        let U : Real := ((10 ^ j.val : Nat) : Real)
        ((orientedLineNormalizedSecondMomentClass length C D V j).card : Real) ≤
          X ^ rho * min ((C.card : Real) ^ 2) (M ^ 4) *
            (V ^ 3 / U + V ^ 4 / M + U * V ^ 5 / X) := by
  obtain ⟨lengthClass, hclass⟩ :=
    exists_card_lineCongruenceHeightClass_le_threshold
      (rho / 8) (by positivity)
  obtain ⟨lengthDivisor, hdivisor⟩ :=
    exists_card_int_divisorsAntidiag_le_decimalPower_rpow_threshold
      (rho / 12) 6 3 (by positivity) (by norm_num)
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hgrowth :
      Tendsto
        (fun length : Nat =>
          ((10 ^ length : Nat) : Real) ^ (rho / 2))
        atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < rho / 2)).comp hscale
  obtain ⟨lengthFixed, hfixed⟩ :=
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 221184000)
  refine ⟨max lengthClass (max lengthDivisor lengthFixed), ?_⟩
  intro length hlength C V k j hV hVX
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let M : Real := ((10 ^ k.2.val : Nat) : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let H : Real := (C.card : Real)
  let P : Real := min (H ^ 2) (M ^ 4)
  let S : Real := V ^ 3 / U + V ^ 4 / M + U * V ^ 5 / X
  let Q : Real := X ^ (rho / 12)
  have hlengthClass : lengthClass ≤ length :=
    (le_max_left _ _).trans hlength
  have hlengthDivisor : lengthDivisor ≤ length :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlength)
  have hlengthFixed : lengthFixed ≤ length :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlength)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hQ : 0 ≤ Q := Real.rpow_nonneg hX.le _
  have hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * X ^ 3 ->
      (z.divisorsAntidiag.card : Real) ≤ Q := by
    intro z hz
    exact hdivisor length hlengthDivisor z (by
      simpa only [X] using hz)
  have hfinite :=
    orientedLineNormalizedSecondMomentClass_card_real_le_large_height
      C V Q k j hV hVX hQ (by
        intro z hz
        exact hfactor z (by simpa only [X] using hz))
  have hclassAtScale : (D.card : Real) ≤
      X ^ (rho / 8) * min H (M ^ 2) := by
    simpa only [D, X, M, H] using hclass length hlengthClass C k
  have hminNonneg : 0 ≤ min H (M ^ 2) := by positivity
  have hminSq : (min H (M ^ 2)) ^ 2 ≤ P := by
    dsimp only [P]
    apply le_min
    · exact pow_le_pow_left₀ hminNonneg (min_le_left _ _) 2
    · have hminM : min H (M ^ 2) ≤ M ^ 2 := min_le_right _ _
      have hsquare := pow_le_pow_left₀ hminNonneg hminM 2
      nlinarith
  have hXClassSq : (X ^ (rho / 8)) ^ 2 = X ^ (rho / 4) := by
    calc
      (X ^ (rho / 8)) ^ 2 =
          X ^ (rho / 8) * X ^ (rho / 8) := by ring
      _ = X ^ (rho / 8 + rho / 8) := (Real.rpow_add hX _ _).symm
      _ = X ^ (rho / 4) := by congr 1; ring
  have hclassSq : (D.card : Real) ^ 2 ≤ X ^ (rho / 4) * P := by
    calc
      (D.card : Real) ^ 2 ≤
          (X ^ (rho / 8) * min H (M ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hclassAtScale 2
      _ = (X ^ (rho / 8)) ^ 2 * (min H (M ^ 2)) ^ 2 := by ring
      _ ≤ X ^ (rho / 4) * P := by
        rw [hXClassSq]
        exact mul_le_mul_of_nonneg_left hminSq (Real.rpow_nonneg hX.le _)
  have hQcube : Q ^ 3 = X ^ (rho / 4) := by
    calc
      Q ^ 3 = (X ^ (rho / 12)) ^ (3 : Real) := by
        rw [show (3 : Real) = (3 : Nat) by norm_num]
        exact (Real.rpow_natCast (X ^ (rho / 12)) 3).symm
      _ = X ^ ((rho / 12) * 3) :=
        (Real.rpow_mul hX.le (rho / 12) 3).symm
      _ = X ^ (rho / 4) := by congr 1; ring
  have hquarter :
      X ^ (rho / 4) * X ^ (rho / 4) = X ^ (rho / 2) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hfixedAtScale : (221184000 : Real) ≤ X ^ (rho / 2) := by
    simpa only [X] using hfixed length hlengthFixed
  have hterms :
      V ^ 3 / U + 6 * V ^ 4 / M + 36 * U * V ^ 5 / X ≤ 36 * S := by
    have h1 : 0 ≤ V ^ 3 / U := by positivity
    have h2 : 0 ≤ V ^ 4 / M := by positivity
    have h3 : 0 ≤ U * V ^ 5 / X := by positivity
    dsimp only [S]
    calc
      V ^ 3 / U + 6 * V ^ 4 / M + 36 * U * V ^ 5 / X =
          V ^ 3 / U + 6 * (V ^ 4 / M) +
            36 * (U * V ^ 5 / X) := by ring
      _ ≤ 36 * (V ^ 3 / U + V ^ 4 / M + U * V ^ 5 / X) := by
        nlinarith
  dsimp only [D, X, M, U] at hfinite ⊢
  dsimp only [D, X, M, U, H, P, S, Q] at hclassSq hQcube hquarter hfixedAtScale hterms
  rw [hQcube] at hfinite
  calc
    ((orientedLineNormalizedSecondMomentClass length C
        (lineCongruenceHeightClass length C k) V j).card : Real) ≤
      6144000 *
        ((lineCongruenceHeightClass length C k).card : Real) ^ 2 *
        (((10 ^ length : Nat) : Real) ^ (rho / 4)) *
        (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          6 * V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          36 * ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real)) := hfinite
    _ ≤ 6144000 *
        ((((10 ^ length : Nat) : Real) ^ (rho / 4)) *
          min ((C.card : Real) ^ 2)
            (((10 ^ k.2.val : Nat) : Real) ^ 4)) *
        (((10 ^ length : Nat) : Real) ^ (rho / 4)) *
        (36 * (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real))) := by
      gcongr
    _ = 221184000 *
        ((((10 ^ length : Nat) : Real) ^ (rho / 4)) *
          (((10 ^ length : Nat) : Real) ^ (rho / 4))) *
        min ((C.card : Real) ^ 2)
          (((10 ^ k.2.val : Nat) : Real) ^ 4) *
        (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real)) := by ring
    _ = 221184000 * (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        min ((C.card : Real) ^ 2)
          (((10 ^ k.2.val : Nat) : Real) ^ 4) *
        (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real)) := by rw [hquarter]
    _ ≤ (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        min ((C.card : Real) ^ 2)
          (((10 ^ k.2.val : Nat) : Real) ^ 4) *
        (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real)) := by gcongr
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        min ((C.card : Real) ^ 2)
          (((10 ^ k.2.val : Nat) : Real) ^ 4) *
        (V ^ 3 / ((10 ^ j.val : Nat) : Real) +
          V ^ 4 / ((10 ^ k.2.val : Nat) : Real) +
          ((10 ^ j.val : Nat) : Real) * V ^ 5 /
            ((10 ^ length : Nat) : Real)) := by
      rw [← Real.rpow_add (by positivity :
        (0 : Real) < ((10 ^ length : Nat) : Real))]
      congr 4
      ring

end PrimesRestrictedDigits
