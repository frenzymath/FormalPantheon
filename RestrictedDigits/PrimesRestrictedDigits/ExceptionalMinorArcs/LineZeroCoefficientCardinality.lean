import PrimesRestrictedDigits.BasicEstimates.DecimalDivisorBound
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientFirstCases
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientLastCases
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientSecondCase
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cardinality of the zero-coefficient plane-pair cover

This combines the four repaired coordinate cases in equation `(15.1)` of
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--211, and then absorbs the
uniform signed divisor bound at decimal scales.
-/

open Filter

namespace PrimesRestrictedDigits

/-- Explicit finite form of the zero-term estimate. The factor-pair bound is
uniform over every signed target in the displayed quadratic envelope. -/
theorem zeroTermLowHeightPlanePairCover_card_real_le
    {X : Nat} (C : Finset (Fin X)) (V Q : Real)
    (_hX : 0 < X) (hV : 1 <= V) (hVX : V < (X : Real))
    (hQ : 1 <= Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) <= 3 * ((X : Real) ^ 2) ->
      (z.divisorsAntidiag.card : Real) <= Q) :
    ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
      90 * (C.card : Real) * V ^ 2 * Q := by
  classical
  let L : Real := (lineCoefficientBox V).card
  let R : Real := (C.card : Real) * L ^ 2 * Q
  have hVNonneg : 0 <= V := zero_le_one.trans hV
  have hQNonneg : 0 <= Q := zero_le_one.trans hQ
  have hCNonneg : (0 : Real) <= C.card := by positivity
  have hLone : 1 <= L := by
    dsimp only [L]
    rw [card_lineCoefficientBox]
    push_cast
    have hfloor : (0 : Real) <= Nat.floor V := by positivity
    linarith
  have hLNonneg : 0 <= L := zero_le_one.trans hLone
  have hRNonneg : 0 <= R := by
    dsimp only [R]
    positivity
  have hfirst :
      ((zeroFirstCoefficientPlaneWitnesses C V).card : Real) <= R := by
    dsimp only [R, L]
    exact zeroFirstCoefficientPlaneWitnesses_card_real_le
      C V Q hV hVX hQNonneg hfactor
  have hsecond :
      ((zeroSecondCoefficientPlaneWitnesses C V).card : Real) <= R := by
    dsimp only [R, L]
    exact zeroSecondCoefficientPlaneWitnesses_card_real_le
      C V Q hV hVX hQNonneg hfactor
  have hthird :
      ((zeroThirdCoefficientPlaneWitnesses C V).card : Real) <= 2 * R := by
    calc
      ((zeroThirdCoefficientPlaneWitnesses C V).card : Real) <=
          2 * (C.card : Real) *
            ((lineCoefficientBox V).card : Real) ^ 2 * Q :=
        zeroThirdCoefficientPlaneWitnesses_card_real_le
          C V Q hV hVX hQ hfactor
      _ = 2 * R := by dsimp only [R, L]; ring
  have hfourth :
      ((zeroFourthCoefficientPlaneWitnesses C V).card : Real) <= 2 * R := by
    calc
      ((zeroFourthCoefficientPlaneWitnesses C V).card : Real) <=
          2 * (C.card : Real) *
            ((lineCoefficientBox V).card : Real) ^ 2 * Q :=
        zeroFourthCoefficientPlaneWitnesses_card_real_le
          C V Q hV hVX hQ hfactor
      _ = 2 * R := by dsimp only [R, L]; ring
  have hwitnesses :
      ((positiveZeroCoefficientPlaneWitnesses C V).card : Real) <=
        6 * R := by
    have hunionNat :
        ((((zeroFirstCoefficientPlaneWitnesses C V ∪
              zeroSecondCoefficientPlaneWitnesses C V) ∪
            zeroThirdCoefficientPlaneWitnesses C V) ∪
          zeroFourthCoefficientPlaneWitnesses C V).card) <=
            (zeroFirstCoefficientPlaneWitnesses C V).card +
            (zeroSecondCoefficientPlaneWitnesses C V).card +
            (zeroThirdCoefficientPlaneWitnesses C V).card +
            (zeroFourthCoefficientPlaneWitnesses C V).card := by
      have h12 := Finset.card_union_le
        (zeroFirstCoefficientPlaneWitnesses C V)
        (zeroSecondCoefficientPlaneWitnesses C V)
      have h123 := Finset.card_union_le
        (zeroFirstCoefficientPlaneWitnesses C V ∪
          zeroSecondCoefficientPlaneWitnesses C V)
        (zeroThirdCoefficientPlaneWitnesses C V)
      have h1234 := Finset.card_union_le
        ((zeroFirstCoefficientPlaneWitnesses C V ∪
            zeroSecondCoefficientPlaneWitnesses C V) ∪
          zeroThirdCoefficientPlaneWitnesses C V)
        (zeroFourthCoefficientPlaneWitnesses C V)
      omega
    have hunionReal :
        (((((zeroFirstCoefficientPlaneWitnesses C V ∪
                zeroSecondCoefficientPlaneWitnesses C V) ∪
              zeroThirdCoefficientPlaneWitnesses C V) ∪
            zeroFourthCoefficientPlaneWitnesses C V).card : Nat) : Real) <=
          ((zeroFirstCoefficientPlaneWitnesses C V).card : Real) +
          (zeroSecondCoefficientPlaneWitnesses C V).card +
          (zeroThirdCoefficientPlaneWitnesses C V).card +
          (zeroFourthCoefficientPlaneWitnesses C V).card := by
      exact_mod_cast hunionNat
    calc
      ((positiveZeroCoefficientPlaneWitnesses C V).card : Real) =
          (((((zeroFirstCoefficientPlaneWitnesses C V ∪
                  zeroSecondCoefficientPlaneWitnesses C V) ∪
                zeroThirdCoefficientPlaneWitnesses C V) ∪
              zeroFourthCoefficientPlaneWitnesses C V).card : Nat) : Real) := by
        rw [positiveZeroCoefficientPlaneWitnesses_eq_union_cases]
      _ <= ((zeroFirstCoefficientPlaneWitnesses C V).card : Real) +
          (zeroSecondCoefficientPlaneWitnesses C V).card +
          (zeroThirdCoefficientPlaneWitnesses C V).card +
          (zeroFourthCoefficientPlaneWitnesses C V).card := hunionReal
      _ <= 6 * R := by linarith
  have hcoefficientPairs :
      ((zeroCoefficientLowHeightPlanePairs C V).card : Real) <=
        8 * R := by
    have himageNat : (zeroCoefficientLowHeightPlanePairs C V).card <=
        (positiveZeroCoefficientPlaneWitnesses C V).card := by
      rw [zeroCoefficientLowHeightPlanePairs]
      exact Finset.card_image_le
    have himageReal :
        ((zeroCoefficientLowHeightPlanePairs C V).card : Real) <=
          (positiveZeroCoefficientPlaneWitnesses C V).card := by
      exact_mod_cast himageNat
    linarith
  have hzeroElements :
      ((zeroElementPlanePairCover C).card : Real) <= 2 * R := by
    have hzero : ((zeroElementPlanePairCover C).card : Real) <=
        2 * (C.card : Real) := by
      exact_mod_cast card_zeroElementPlanePairCover_le C
    have hLQ : 1 <= L ^ 2 * Q := by
      calc
        (1 : Real) = 1 ^ 2 * 1 := by norm_num
        _ <= L ^ 2 * Q := by gcongr
    calc
      ((zeroElementPlanePairCover C).card : Real) <=
          2 * (C.card : Real) := hzero
      _ = 2 * (C.card : Real) * 1 := by ring
      _ <= 2 * (C.card : Real) * (L ^ 2 * Q) := by gcongr
      _ = 2 * R := by dsimp only [R]; ring
  have hcover :
      ((zeroTermLowHeightPlanePairCover C V).card : Real) <= 10 * R := by
    have hunionNat : (zeroTermLowHeightPlanePairCover C V).card <=
        (zeroElementPlanePairCover C).card +
          (zeroCoefficientLowHeightPlanePairs C V).card := by
      simpa only [zeroTermLowHeightPlanePairCover] using
        Finset.card_union_le (zeroElementPlanePairCover C)
          (zeroCoefficientLowHeightPlanePairs C V)
    have hunionReal :
        ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
          (zeroElementPlanePairCover C).card +
            (zeroCoefficientLowHeightPlanePairs C V).card := by
      exact_mod_cast hunionNat
    linarith
  have hLUpper : L <= 3 * V := by
    dsimp only [L]
    exact card_lineCoefficientBox_real_le hV
  have hsumNonneg : 0 <= 3 * V + L := by positivity
  have hproductNonneg : 0 <= (3 * V - L) * (3 * V + L) :=
    mul_nonneg (sub_nonneg.mpr hLUpper) hsumNonneg
  have hLSq : L ^ 2 <= 9 * V ^ 2 := by nlinarith
  have hRScale : R <= 9 * (C.card : Real) * V ^ 2 * Q := by
    dsimp only [R]
    calc
      (C.card : Real) * L ^ 2 * Q <=
          (C.card : Real) * (9 * V ^ 2) * Q := by gcongr
      _ = 9 * (C.card : Real) * V ^ 2 * Q := by ring
  calc
    ((zeroTermLowHeightPlanePairCover C V).card : Real) <= 10 * R := hcover
    _ <= 10 * (9 * (C.card : Real) * V ^ 2 * Q) := by gcongr
    _ = 90 * (C.card : Real) * V ^ 2 * Q := by ring

/-- Coefficient-one decimal-scale form of the source zero-term estimate. The
threshold depends only on the requested positive exponent. -/
theorem exists_card_zeroTermLowHeightPlanePairCover_le_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real),
        1 <= V -> V < ((10 ^ length : Nat) : Real) ->
        ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
          (((10 ^ length : Nat) : Real) ^ rho) *
            (C.card : Real) * V ^ 2 := by
  obtain ⟨lengthDivisor, hdivisor⟩ :=
    exists_card_int_divisorsAntidiag_le_decimalPower_rpow_threshold
      (rho / 2) 3 2 (by positivity) (by norm_num)
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
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 90)
  refine ⟨max lengthDivisor lengthFixed, ?_⟩
  intro length hlength C V hV hVX
  let X : Nat := 10 ^ length
  let XR : Real := (X : Real)
  have hlengthDivisor : lengthDivisor <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFixed : lengthFixed <= length :=
    (le_max_right _ _).trans hlength
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  have hXOne : 1 <= X := hX
  have hXROne : (1 : Real) <= XR := by
    dsimp only [XR]
    exact_mod_cast hXOne
  have hQ : 1 <= XR ^ (rho / 2) := by
    exact Real.one_le_rpow hXROne (by positivity)
  have hfactor : forall z : Int,
      (z.natAbs : Real) <= 3 * XR ^ 2 ->
      (z.divisorsAntidiag.card : Real) <= XR ^ (rho / 2) := by
    intro z hz
    apply hdivisor length hlengthDivisor
    simpa only [X, XR] using hz
  have hfinite :
      ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
        90 * (C.card : Real) * V ^ 2 * XR ^ (rho / 2) := by
    simpa only [X, XR] using
      zeroTermLowHeightPlanePairCover_card_real_le
        C V (XR ^ (rho / 2)) hX hV hVX hQ hfactor
  have hfixedAtScale : (90 : Real) <= XR ^ (rho / 2) := by
    simpa only [X, XR] using hfixed length hlengthFixed
  have htailNonneg :
      0 <= (C.card : Real) * V ^ 2 * XR ^ (rho / 2) := by positivity
  have hXRPos : 0 < XR := by
    dsimp only [XR]
    positivity
  dsimp only [X, XR] at hfinite hfixedAtScale htailNonneg hXRPos ⊢
  calc
    ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
        90 * (C.card : Real) * V ^ 2 *
          (((10 ^ length : Nat) : Real) ^ (rho / 2)) := hfinite
    _ = 90 * ((C.card : Real) * V ^ 2 *
        (((10 ^ length : Nat) : Real) ^ (rho / 2))) := by ring
    _ <= (((10 ^ length : Nat) : Real) ^ (rho / 2)) *
        ((C.card : Real) * V ^ 2 *
          (((10 ^ length : Nat) : Real) ^ (rho / 2))) :=
      mul_le_mul_of_nonneg_right hfixedAtScale htailNonneg
    _ = ((((10 ^ length : Nat) : Real) ^ (rho / 2)) *
          (((10 ^ length : Nat) : Real) ^ (rho / 2))) *
        (C.card : Real) * V ^ 2 := by ring
    _ = (((10 ^ length : Nat) : Real) ^ rho) *
        (C.card : Real) * V ^ 2 := by
      rw [← Real.rpow_add hXRPos]
      congr 3
      ring

end PrimesRestrictedDigits
