import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeContinuationBuchstab
import PrimesRestrictedDigits.SieveDecomposition.RoughBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite lower bounds for the low central-large continuations

The strict cofactor carrier is bounded with the uniform parameter range `1 <= t <= 400`. Its
unit cofactor remains in the full sifted term; only the nonnegative restricted cardinality is
discarded in the lower-bound direction.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eqs. (6.10)--(6.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralLargeContinuationFinitePairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

private theorem sectionSixFirstLowCentralLargeContinuation_primeData
    {epsilon : Real} {length : Nat}
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    index.1.1.Prime ∧ index.1.2.Prime ∧ index.2.Prime := by
  have hpiece :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
  have hr := (mem_sievePrimeInterval.mp hcontinuation.2).1
  have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
  have hpqPiece : index.1 ∈
      sectionSixFirstLowStrictIndices epsilon length := by
    simpa [sectionSixFirstPairMem] using hpqFiltered.2.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece
  exact ⟨(mem_sievePrimeInterval.mp hpqData.1).1,
    (mem_sievePrimeInterval.mp hpqData.2).1, hr⟩

private theorem sectionSixFirstLowCentralLargeContinuation_term_lower
    {C : Real} (hrough :
      ∀ Y y t : Real, 0 < Y -> 2 <= y -> 1 <= t -> t <= 400 ->
        t = Real.log Y / Real.log y ->
        (maynardStrictRoughCount Y y : Real) <=
          buchstabFunction t * Y / Real.log y +
            C * (Y / Real.log Y ^ 2))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let densityMass : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real)
    (-densityMass *
        (buchstabFunction
              (Real.log (X /
                  ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
                Real.log (index.2 : Real)) /
            ((index.1.1 : Real) * (index.1.2 : Real) *
              (index.2 : Real) * Real.log (index.2 : Real)) +
          C / ((index.1.1 : Real) * (index.1.2 : Real) *
            (index.2 : Real) *
            Real.log (X /
              ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2))) <=
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1
  let q : Nat := index.1.2
  let r : Nat := index.2
  let pairD : PNat := sectionSixFirstPairModulus index.1
  let d : PNat := pairD * Nat.toPNat' r
  let Y : Real := X / ((p * q * r : Nat) : Real)
  let t : Real := Real.log Y / Real.log (r : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let lambda : Real := densityMass / X
  have hprime := sectionSixFirstLowCentralLargeContinuation_primeData hindex
  have hp : p.Prime := by simpa only [p] using hprime.1
  have hq : q.Prime := by simpa only [q] using hprime.2.1
  have hr : r.Prime := by simpa only [r] using hprime.2.2
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hparameter :=
    sectionSixFirstLowCentralLargeContinuation_buchstabParameter_bounds
      hepsilon hepsilonSmall hlength hindex
  have hY : 0 < Y := by
    simpa only [X, XNat, Y, p, q, r] using hparameter.1
  have hrTwo : (2 : Real) <= r := by
    simpa only [r] using hparameter.2.1
  have htOne : 1 <= t := by
    simpa only [X, XNat, Y, p, q, r, t] using hparameter.2.2.1
  have htFourHundred : t <= 400 := by
    simpa only [X, XNat, Y, p, q, r, t] using hparameter.2.2.2
  have hlogr : 0 < Real.log (r : Real) :=
    Real.log_pos (by exact_mod_cast hr.one_lt)
  have hlogY : 0 < Real.log Y := by
    have hlog := (le_div_iff₀ hlogr).1 htOne
    linarith
  have hroughAt := hrough Y (r : Real) t hY hrTwo htOne
    htFourHundred rfl
  have hd : (d : Real) = (p : Real) * q * r := by
    dsimp only [d, pairD]
    simp only [PNat.mul_coe, Nat.toPNat'_coe, if_pos hr.pos,
      sectionSixFirstPairModulus, Nat.cast_mul]
    dsimp only [p, q]
    rw [if_pos hp.pos, if_pos hq.pos]
  have hterm : sectionSixStrictPrimeTerm digit length pairD r =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (r : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (r : Real) : Real) := by
    rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length pairD hr,
      sectionSixSiftedSum_eq_card_sub_density_mul_card,
      card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier d hrTwo]
    simp only [d, lambda, densityMass, X, XNat, div_eq_mul_inv, mul_assoc]
    rw [hd]
    congr 2
    dsimp only [Y, X, XNat]
    norm_num only [Nat.cast_mul]
    field_simp [hpPos.ne', hqPos.ne', hrPos.ne']
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, densityMass, X]
    exact div_nonneg (mul_nonneg hdensity (by positivity)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hroughAt hlambda
  have hmainScale : lambda *
      (buchstabFunction t * Y / Real.log (r : Real) +
        C * (Y / Real.log Y ^ 2)) =
      densityMass *
        (buchstabFunction t /
            ((p : Real) * q * r * Real.log (r : Real)) +
          C / ((p : Real) * q * r * Real.log Y ^ 2)) := by
    dsimp only [lambda, densityMass, Y, X]
    norm_num only [Nat.cast_mul]
    field_simp [hX.ne', hpPos.ne', hqPos.ne', hrPos.ne',
      hlogr.ne', hlogY.ne']
  dsimp only [X, XNat, densityMass]
  rw [show sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2 =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (r : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (r : Real) : Real) by
      simpa only [pairD, r] using hterm]
  have hrestricted : 0 <=
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (r : Real)).card : Real) := by positivity
  have hscaled' : lambda *
      (maynardStrictRoughCount Y (r : Real) : Real) <=
      densityMass *
        (buchstabFunction t /
            ((p : Real) * q * r * Real.log (r : Real)) +
          C / ((p : Real) * q * r * Real.log Y ^ 2)) := by
    rw [← hmainScale]
    exact hscaled
  dsimp only [t, Y, p, q, r] at hscaled' ⊢
  nlinarith

theorem
    exists_sectionSixFirstLowCentralLargeContinuationFiniteLowerConstant :
    ∃ C : Real, 0 < C ∧
      ∀ (epsilon : Real), 0 < epsilon -> epsilon <= 1 / 64 ->
        ∀ {length : Nat}, 1 <= length -> ∀ (digit : Fin 10)
          (piece : SectionSixFirstLowCentralLargeContinuationPiece),
          let densityMass : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real)
          (-densityMass *
              (sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
                  epsilon length piece +
                C *
                  sectionSixFirstLowCentralLargeContinuationRoughErrorSum
                    epsilon length piece)) <=
            sectionSixFirstLowCentralLargeStrictPieceSum
              epsilon digit length piece := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_maynardStrictRoughCount_upper 400 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall length hlength digit piece
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let indices := sectionSixFirstLowCentralLargeContinuationPieceIndices
    epsilon length piece
  have hpoint : ∀ index ∈ indices,
      -densityMass *
          (buchstabFunction
                (Real.log (X /
                    ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
                  Real.log (index.2 : Real)) /
              ((index.1.1 : Real) * (index.1.2 : Real) *
                (index.2 : Real) * Real.log (index.2 : Real)) +
            C / ((index.1.1 : Real) * (index.1.2 : Real) *
              (index.2 : Real) *
              Real.log (X /
                ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2)) <=
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2 := by
    intro index hindex
    simpa only [densityMass, X, indices] using
      sectionSixFirstLowCentralLargeContinuation_term_lower hrough
        hepsilon hepsilonSmall hlength digit hindex
  dsimp only
  unfold sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
    sectionSixFirstLowCentralLargeContinuationRoughErrorSum
    sectionSixFirstLowCentralLargeStrictPieceSum
  change -densityMass *
      ((∑ index ∈ indices,
        buchstabFunction
            (Real.log (X /
                ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
              Real.log (index.2 : Real)) /
          ((index.1.1 : Real) * (index.1.2 : Real) *
            (index.2 : Real) * Real.log (index.2 : Real))) +
      C * (∑ index ∈ indices,
        1 / ((index.1.1 : Real) * (index.1.2 : Real) *
          (index.2 : Real) *
          Real.log (X /
            ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2))) <=
    ∑ index ∈ indices,
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2
  calc
    _ = ∑ index ∈ indices,
        -densityMass *
          (buchstabFunction
                (Real.log (X /
                    ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
                  Real.log (index.2 : Real)) /
              ((index.1.1 : Real) * (index.1.2 : Real) *
                (index.2 : Real) * Real.log (index.2 : Real)) +
            C / ((index.1.1 : Real) * (index.1.2 : Real) *
              (index.2 : Real) *
              Real.log (X /
                ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2)) := by
      rw [← Finset.mul_sum]
      apply congrArg (fun value : Real => -densityMass * value)
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro index _hindex
      ring
    _ <= _ := Finset.sum_le_sum fun index hindex => hpoint index hindex

theorem sectionSixFirstLowCentralLargeContinuation_lower_of_bounds
    {C epsilon rho integral normalized : Real}
    (hC : 0 <= C) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece)
    (hmain :
      sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
          epsilon length piece =
        normalized / Real.log ((10 ^ length : Nat) : Real))
    (hnormalized : normalized <= integral + rho / 2)
    (herrorSmall :
      C * (2 * Real.log 4) ^ 3 /
          (sectionSixThetaGap epsilon ^ 5 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2)
    (hfinite :
      let densityMass : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real)
      (-densityMass *
          (sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
              epsilon length piece +
            C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
              epsilon length piece)) <=
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
    (-scale * (integral + rho)) <=
      sectionSixFirstLowCentralLargeStrictPieceSum
        epsilon digit length piece := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (Nat.ne_of_gt hlength)
      (by norm_num : 1 < (10 : Nat))
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hdensityMass : 0 <= densityMass := by
    dsimp only [densityMass]
    exact mul_nonneg hdensity (by positivity)
  have herror :=
    sectionSixFirstLowCentralLargeContinuationRoughErrorSum_le
      epsilon hepsilon hepsilonSmall hlength piece
  have herrorScaled :
      C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
          epsilon length piece <=
        (rho / 2) / Real.log X := by
    calc
      C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
          epsilon length piece <=
          C * ((2 * Real.log 4) ^ 3 /
            (sectionSixThetaGap epsilon ^ 5 * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using herror) hC
      _ = (C * (2 * Real.log 4) ^ 3 /
          (sectionSixThetaGap epsilon ^ 5 * Real.log X)) /
            Real.log X := by
        field_simp [hgap.ne', hlogX.ne']
      _ <= (rho / 2) / Real.log X :=
        div_le_div_of_nonneg_right
          (by simpa only [X] using herrorSmall) hlogX.le
  have hbracket :
      sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
          epsilon length piece +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length piece <=
        (integral + rho) / Real.log X := by
    rw [hmain]
    calc
      normalized / Real.log X +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length piece <=
        (integral + rho / 2) / Real.log X +
          (rho / 2) / Real.log X :=
        add_le_add (div_le_div_of_nonneg_right hnormalized hlogX.le)
          herrorScaled
      _ = (integral + rho) / Real.log X := by ring
  dsimp only
  change -(densityMass / Real.log X) * (integral + rho) <= _
  calc
    -(densityMass / Real.log X) * (integral + rho) =
      -densityMass * ((integral + rho) / Real.log X) := by ring
    _ <= -densityMass *
        (sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
            epsilon length piece +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length piece) := by
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_left hbracket hdensityMass)
    _ <= sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length piece := by
      simpa only [densityMass] using hfinite

end

end PrimesRestrictedDigits
