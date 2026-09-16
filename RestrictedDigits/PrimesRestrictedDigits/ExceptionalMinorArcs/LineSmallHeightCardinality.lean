import PrimesRestrictedDigits.BasicEstimates.DecimalDivisorBound
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightLinearFibers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr

/-!
# Cardinality of the small primitive-height normalized class

This combines the seven exact prefix bounds and proves the coefficient-one decimal-scale form
of equation `(15.4)` in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212.
-/

open Filter

namespace PrimesRestrictedDigits

/-- Explicit finite form of the small primitive-height count. All four signed
divisor fibers use one uniform target envelope. -/
theorem orientedLineNormalizedSecondMomentClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length)))
    (V Q : Real) (j : Fin (length + 1))
    (hV : 1 ≤ V) (hVX : V < ((10 ^ length : Nat) : Real))
    (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤
          6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    ((orientedLineNormalizedSecondMomentClass
        length C D V j).card : Real) ≤
      345600 * (D.card : Real) *
        ((10 ^ j.val : Nat) : Real) * V ^ 5 * Q ^ 4 := by
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let B : Real :=
    ((lineCoefficientBox (2 * U * V)).card : Real)
  let R : Real := 40 * V / U
  have hUOne : 1 ≤ U := by
    dsimp only [U]
    rw [Nat.cast_pow]
    exact one_le_pow₀ (by norm_num)
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hV)) hUPos.le
  have hUVOne : 1 ≤ U * V := by
    simpa only [one_mul] using
      mul_le_mul hUOne hV (by norm_num : (0 : Real) ≤ 1)
        (zero_le_one.trans hUOne)
  have hWOne : 1 ≤ 2 * U * V := by nlinarith
  have hB : B ≤ 6 * U * V := by
    have hbox := card_lineCoefficientBox_real_le hWOne
    dsimp only [B] at hbox ⊢
    nlinarith
  have h0 := lineSmallHeightKeyClass_card_real_le C D V j hV
  have h1 := lineSmallHeightCrossFactorClass_card_real_le
    C D V Q j hV hVX hQ hfactor
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
        (D.card : Real) * B ^ 3 * Q ^ 4 * R ^ 2 := by
    calc
      ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
          ((lineSmallHeightFourthPairClass length C D V j).card : Real) * Q :=
        h6
      _ ≤ (((lineSmallHeightThirdPairClass length C D V j).card : Real) * R) *
          Q := by simpa only [R, U] using mul_le_mul_of_nonneg_right h5 hQ
      _ ≤ ((((lineSmallHeightSecondPrimitiveFactorClass
          length C D V j).card : Real) * R) * R) * Q := by
        gcongr
      _ ≤ (((((lineSmallHeightFirstPrimitiveFactorClass
          length C D V j).card : Real) * Q) * R) * R) * Q := by
        gcongr
      _ ≤ ((((((lineSmallHeightCrossFactorClass
          length C D V j).card : Real) * Q) * Q) * R) * R) * Q := by
        gcongr
      _ ≤ (((((((lineSmallHeightKeyClass
          length C D V j).card : Real) * Q) * Q) * Q) * R) * R) * Q := by
        gcongr
      _ ≤ (((((((D.card : Real) * B ^ 3) * Q) * Q) * Q) * R) * R) * Q := by
        have h0' : ((lineSmallHeightKeyClass length C D V j).card : Real) ≤
            (D.card : Real) * B ^ 3 := by simpa only [B, U] using h0
        gcongr
      _ = (D.card : Real) * B ^ 3 * Q ^ 4 * R ^ 2 := by ring
  have hcodeFinal :
      ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
        345600 * (D.card : Real) * U * V ^ 5 * Q ^ 4 := by
    calc
      ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
          (D.card : Real) * B ^ 3 * Q ^ 4 * R ^ 2 := hcode
      _ ≤ (D.card : Real) * (6 * U * V) ^ 3 * Q ^ 4 * R ^ 2 := by
        gcongr
      _ = 345600 * (D.card : Real) * U * V ^ 5 * Q ^ 4 := by
        dsimp only [R]
        field_simp [hUPos.ne']
        ring
  have hcardEq :
      ((orientedLineNormalizedSecondMomentClass
          length C D V j).card : Real) =
        ((lineSmallHeightCodeClass length C D V j).card : Real) := by
    exact_mod_cast (card_lineSmallHeightCodeClass C D V j).symm
  rw [hcardEq]
  simpa only [U] using hcodeFinal

/-- Coefficient-one decimal-scale form of the source small-height estimate.
The threshold depends only on the requested positive exponent. -/
theorem
    exists_card_orientedLineNormalizedSecondMomentClass_le_small_height_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 ≤ length ->
      forall (C D : Finset (Fin (10 ^ length))) (V : Real)
        (j : Fin (length + 1)),
        1 ≤ V -> V < ((10 ^ length : Nat) : Real) ->
        ((orientedLineNormalizedSecondMomentClass
            length C D V j).card : Real) ≤
          (((10 ^ length : Nat) : Real) ^ rho) *
            (D.card : Real) * ((10 ^ j.val : Nat) : Real) * V ^ 5 := by
  obtain ⟨lengthDivisor, hdivisor⟩ :=
    exists_card_int_divisorsAntidiag_le_decimalPower_rpow_threshold
      (rho / 8) 6 3 (by positivity) (by norm_num)
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
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 345600)
  refine ⟨max lengthDivisor lengthFixed, ?_⟩
  intro length hlength C D V j hV hVX
  let X : Nat := 10 ^ length
  let XR : Real := (X : Real)
  have hlengthDivisor : lengthDivisor ≤ length :=
    (le_max_left _ _).trans hlength
  have hlengthFixed : lengthFixed ≤ length :=
    (le_max_right _ _).trans hlength
  have hXOne : 1 ≤ X := by
    dsimp only [X]
    exact one_le_pow₀ (by norm_num)
  have hXROne : (1 : Real) ≤ XR := by
    dsimp only [XR]
    exact_mod_cast hXOne
  have hXRPos : 0 < XR := zero_lt_one.trans_le hXROne
  let Q : Real := XR ^ (rho / 8)
  have hQ : 0 ≤ Q := Real.rpow_nonneg hXRPos.le _
  have hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * XR ^ 3 ->
      (z.divisorsAntidiag.card : Real) ≤ Q := by
    intro z hz
    apply hdivisor length hlengthDivisor
    simpa only [X, XR, Q] using hz
  have hfinite :
      ((orientedLineNormalizedSecondMomentClass
          length C D V j).card : Real) ≤
        345600 * (D.card : Real) *
          ((10 ^ j.val : Nat) : Real) * V ^ 5 * Q ^ 4 :=
    orientedLineNormalizedSecondMomentClass_card_real_le
      C D V Q j hV hVX hQ hfactor
  have hQpow : Q ^ 4 = XR ^ (rho / 2) := by
    dsimp only [Q]
    calc
      (XR ^ (rho / 8)) ^ (4 : Nat) =
          (XR ^ (rho / 8)) ^ (4 : Real) :=
        (Real.rpow_natCast (XR ^ (rho / 8)) 4).symm
      _ = XR ^ ((rho / 8) * 4) :=
        (Real.rpow_mul hXRPos.le (rho / 8) 4).symm
      _ = XR ^ (rho / 2) := by
        congr 1
        ring
  have hfixedAtScale : (345600 : Real) ≤ XR ^ (rho / 2) := by
    simpa only [X, XR] using hfixed length hlengthFixed
  have htailNonneg :
      0 ≤ (D.card : Real) * ((10 ^ j.val : Nat) : Real) *
        V ^ 5 * XR ^ (rho / 2) := by positivity
  rw [hQpow] at hfinite
  dsimp only [X, XR] at hfinite hfixedAtScale htailNonneg hXRPos ⊢
  calc
    ((orientedLineNormalizedSecondMomentClass
        length C D V j).card : Real) ≤
      345600 * (D.card : Real) * ((10 ^ j.val : Nat) : Real) *
        V ^ 5 * (((10 ^ length : Nat) : Real) ^ (rho / 2)) := hfinite
    _ = 345600 * ((D.card : Real) * ((10 ^ j.val : Nat) : Real) *
        V ^ 5 * (((10 ^ length : Nat) : Real) ^ (rho / 2))) := by ring
    _ ≤ (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        ((D.card : Real) * ((10 ^ j.val : Nat) : Real) *
          V ^ 5 * (((10 ^ length : Nat) : Real) ^ (rho / 2))) :=
      mul_le_mul_of_nonneg_right hfixedAtScale htailNonneg
    _ = ((((10 ^ length : Nat) : Real) ^ (rho / 2)) *
          (((10 ^ length : Nat) : Real) ^ (rho / 2))) *
        (D.card : Real) * ((10 ^ j.val : Nat) : Real) * V ^ 5 := by ring
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        (D.card : Real) * ((10 ^ j.val : Nat) : Real) * V ^ 5 := by
      rw [← Real.rpow_add hXRPos]
      congr 4
      ring

end PrimesRestrictedDigits
