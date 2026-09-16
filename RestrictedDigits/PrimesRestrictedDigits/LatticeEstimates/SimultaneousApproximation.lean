import PrimesRestrictedDigits.LatticeEstimates.CrossProductWitness
import PrimesRestrictedDigits.LatticeEstimates.RationalNormalization

/-!
# Simultaneous approximation from a rank-two lattice

This is the repaired formalization of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1,
pp. 198--201. The proof retains the full printed parameter range; in
particular, it does not insert the false unstated assumption `delta<=N`.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/--
Explicit quantitative kernel of Maynard's Lemma 14.1. The source writes three absolute implied
constants; the proof permits the common value `10^6`.
-/
theorem latticeSimultaneousApproximation
    {X : Nat} (a1 a2 : Fin X) (N K delta : Real)
    (Lambda : RankTwoIntegralLattice)
    (hX : 1 <= X) (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / (X : Real) <= delta)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists q : Nat, 0 < q ∧
      (q : Real) <= 1000000 * (X : Real) / (N * K) ∧
      exists b1 b2 : Int,
        |(((a1 : Nat) : Real) / (X : Real) -
          (b1 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) ∧
        |(((a2 : Nat) : Real) / (X : Real) -
          (b2 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hXReal : 0 < (X : Real) := by exact_mod_cast hXpos
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  by_cases hsmall : N * K <= 1000000
  · exact exists_trivial_latticeSimultaneousApproximation
      hXpos a1 a2 N K hNpos hKpos hsmall
  have hlarge : 1000000 < N * K := lt_of_not_ge hsmall
  obtain ⟨c, hc, hcnorm, lambda, hresidual⟩ :=
    exists_integralCrossProduct_with_bounds
      hXpos a1 a2 delta N K hdelta hN hK Lambda hcard hnonlinear
  have hquarter :
      ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <
        (X : Real) / 4 :=
    residual_lt_quarter_of_million_lt_product
      hXpos N K c hc
        (latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c)
      hlarge hresidual
  have hcTwo : c 2 ≠ 0 :=
    integerVector_third_ne_zero_of_residual_lt
      hXpos a1 a2 c lambda hquarter
  have hdominant : forall i : Fin 2,
      |((c i.castSucc : Int) : Real)| <= 2 * |((c 2 : Int) : Real)| :=
    abs_first_coordinates_le_two_mul_third_of_residual_lt
      hXpos a1 a2 c lambda hquarter
  let q := integerVectorDenominator c
  let b1 := signedIntegerVectorNumerator c 0
  let b2 := signedIntegerVectorNumerator c 1
  have hqpos : 0 < q := by
    simpa [q] using integerVectorDenominator_pos hcTwo
  have hqNorm : (q : Real) <= ‖intVectorToEuclidean c‖ := by
    calc
      (q : Real) = |((c 2 : Int) : Real)| := by
        simp [q, cast_integerVectorDenominator]
      _ <= ‖intVectorToEuclidean c‖ := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le (intVectorToEuclidean c) 2
  have hNX : N <= delta * (X : Real) :=
    (div_le_iff₀ hXReal).mp hdeltaLower
  have hscale : 705600 / (delta * K) <=
      705600 * (X : Real) / (N * K) := by
    apply (div_le_div_iff₀ (mul_pos hdelta hKpos) (mul_pos hNpos hKpos)).2
    calc
      705600 * (N * K) <= 705600 * ((delta * (X : Real)) * K) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hNX hKpos.le) (by norm_num)
      _ = (705600 * (X : Real)) * (delta * K) := by ring
  have hconstant : 705600 * (X : Real) / (N * K) <=
      1000000 * (X : Real) / (N * K) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (705600 : Real) <= 1000000)
        hXReal.le)
      (mul_pos hNpos hKpos).le
  have hqBound : (q : Real) <= 1000000 * (X : Real) / (N * K) :=
    hqNorm.trans (hcnorm.trans (hscale.trans hconstant))
  have hdominantZero : |((c 0 : Int) : Real)| <=
      2 * |((c 2 : Int) : Real)| := by
    simpa using hdominant 0
  have hdominantOne : |((c 1 : Int) : Real)| <=
      2 * |((c 2 : Int) : Real)| := by
    simpa using hdominant 1
  have herrorZero :=
    abs_angleRatio_sub_integerRatio_le_fourHundredFiftyThreeThousandSixHundred
      hXpos a1 a2 N K hNpos hKpos c lambda 0 hcTwo hdominantZero hresidual
  have herrorOne :=
    abs_angleRatio_sub_integerRatio_le_fourHundredFiftyThreeThousandSixHundred
      hXpos a1 a2 N K hNpos hKpos c lambda 1 hcTwo hdominantOne hresidual
  have hratioZero : (b1 : Real) / (q : Real) =
      ((c 0 : Int) : Real) / ((c 2 : Int) : Real) := by
    simpa [b1, q] using
      signedIntegerVectorNumerator_div_denominator c 0 hcTwo
  have hratioOne : (b2 : Real) / (q : Real) =
      ((c 1 : Int) : Real) / ((c 2 : Int) : Real) := by
    simpa [b2, q] using
      signedIntegerVectorNumerator_div_denominator c 1 hcTwo
  refine ⟨q, hqpos, hqBound, b1, b2, ?_, ?_⟩
  · rw [hratioZero]
    have hweaken := herrorZero.trans (by
      apply div_le_div_of_nonneg_right (by norm_num : (453600 : Real) <= 1000000)
      positivity)
    simpa [q] using hweaken
  · rw [hratioOne]
    have hweaken := herrorOne.trans (by
      apply div_le_div_of_nonneg_right (by norm_num : (453600 : Real) <= 1000000)
      positivity)
    simpa [q] using hweaken

/-- The source's asymptotic notation can be witnessed by one positive
constant chosen uniformly before every parameter. -/
theorem exists_latticeSimultaneousApproximationConstant :
    exists C : Real, 0 < C ∧
      forall {X : Nat} (a1 a2 : Fin X) (N K delta : Real)
        (Lambda : RankTwoIntegralLattice),
        1 <= X -> 1 <= N -> 1 <= K -> 0 < delta ->
        N / (X : Real) <= delta ->
        delta * K * N ^ 2 <=
          ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real) ->
        LatticePointsNotContainedInLine
          (latticeGeneratingIntegerPoints a1 a2 Lambda delta N) ->
        exists q : Nat, 0 < q ∧
          (q : Real) <= C * (X : Real) / (N * K) ∧
          exists b1 b2 : Int,
            |(((a1 : Nat) : Real) / (X : Real) -
              (b1 : Real) / (q : Real))| <=
                C / (N * K * (q : Real)) ∧
            |(((a2 : Nat) : Real) / (X : Real) -
              (b2 : Real) / (q : Real))| <=
                C / (N * K * (q : Real)) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro X a1 a2 N K delta Lambda hX hN hK hdelta hdeltaLower hcard hnonlinear
  exact latticeSimultaneousApproximation
    a1 a2 N K delta Lambda hX hN hK hdelta hdeltaLower hcard hnonlinear

/-- Literal power-of-ten specialization matching the paper's global source
domain. The kernel above proves the stronger statement for every `X>=1`. -/
theorem latticeSimultaneousApproximation_powerTen
    (length : Nat) (a1 a2 : Fin (10 ^ length)) (N K delta : Real)
    (Lambda : RankTwoIntegralLattice)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists q : Nat, 0 < q ∧
      (q : Real) <= 1000000 * ((10 ^ length : Nat) : Real) / (N * K) ∧
      exists b1 b2 : Int,
        |(((a1 : Nat) : Real) / ((10 ^ length : Nat) : Real) -
          (b1 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) ∧
        |(((a2 : Nat) : Real) / ((10 ^ length : Nat) : Real) -
          (b2 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) := by
  exact latticeSimultaneousApproximation
    a1 a2 N K delta Lambda (Nat.one_le_pow length 10 (by norm_num)) hN hK hdelta
      hdeltaLower hcard hnonlinear

end PrimesRestrictedDigits
