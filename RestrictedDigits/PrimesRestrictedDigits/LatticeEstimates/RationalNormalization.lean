import PrimesRestrictedDigits.LatticeEstimates.AngleVector
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Rational normalization for the lattice approximation

This isolates the last sign and denominator argument in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 14.1. Lean coordinates `0,1,2` correspond to
the source coordinates `c_1,c_2,c_3`.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The positive denominator obtained from the third integral coordinate. -/
def integerVectorDenominator (c : Fin 3 -> Int) : Nat :=
  (c 2).natAbs

/-- Simultaneously change the signs of the numerator coordinates so that the
third coordinate becomes the positive denominator. -/
def signedIntegerVectorNumerator (c : Fin 3 -> Int) (i : Fin 3) : Int :=
  Int.sign (c 2) * c i

theorem integerVectorDenominator_pos {c : Fin 3 -> Int} (hc : c 2 ≠ 0) :
    0 < integerVectorDenominator c := by
  exact Int.natAbs_pos.mpr hc

@[simp] theorem cast_integerVectorDenominator (c : Fin 3 -> Int) :
    (integerVectorDenominator c : Real) = |((c 2 : Int) : Real)| := by
  simp [integerVectorDenominator, Nat.cast_natAbs, Int.cast_abs]

/-- Signed numerator over the natural denominator is the original ratio of
integer coordinates. -/
theorem signedIntegerVectorNumerator_div_denominator
    (c : Fin 3 -> Int) (i : Fin 3) (hc : c 2 ≠ 0) :
    ((signedIntegerVectorNumerator c i : Int) : Real) /
        (integerVectorDenominator c : Real) =
      ((c i : Int) : Real) / ((c 2 : Int) : Real) := by
  have hcReal : ((c 2 : Int) : Real) ≠ 0 := by exact_mod_cast hc
  have hsign : Int.sign (c 2) ≠ 0 := by
    simpa using hc
  have hsignReal : ((Int.sign (c 2) : Int) : Real) ≠ 0 := by
    exact_mod_cast hsign
  have hdenominator : (integerVectorDenominator c : Real) =
      ((Int.sign (c 2) : Int) : Real) * ((c 2 : Int) : Real) := by
    rw [← Int.cast_mul, Int.sign_mul_self_eq_natAbs]
    rfl
  rw [hdenominator]
  rw [signedIntegerVectorNumerator, Int.cast_mul]
  change (((Int.sign (c 2) : Int) : Real) * ((c i : Int) : Real)) /
      (((Int.sign (c 2) : Int) : Real) * ((c 2 : Int) : Real)) =
        ((c i : Int) : Real) / ((c 2 : Int) : Real)
  field_simp [hcReal, hsignReal]

/-- Every real coordinate of a Euclidean triple is bounded by its norm. -/
theorem abs_euclideanCoordinate_le_norm (v : E) (i : Fin 3) :
    |v i| <= ‖v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i

/-- A residual smaller than `X/4` forces the third integral coordinate of its
axis to be nonzero. -/
theorem integerVector_third_ne_zero_of_residual_lt
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (c : Fin 3 -> Int) (lambda : Real)
    (hresidual :
      ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <
        (X : Real) / 4) :
    c 2 ≠ 0 := by
  intro hc
  have hcoordinate := abs_euclideanCoordinate_le_norm
    (latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c) 2
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  simp [hc, abs_of_pos hXReal] at hcoordinate
  linarith

/-- When the residual from the integer axis is below `X/4`, either of the
first two coordinates has absolute value at most twice the third. -/
theorem abs_integerCoordinate_le_two_mul_third_of_residual_lt
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (c : Fin 3 -> Int) (lambda : Real) (i : Fin 3)
    (hiNonneg : 0 <= latticeAngleVector a1 a2 i)
    (hiLt : latticeAngleVector a1 a2 i < (X : Real))
    (hresidual :
      ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <
        (X : Real) / 4) :
    |((c i : Int) : Real)| <= 2 * |((c 2 : Int) : Real)| := by
  let A := latticeAngleVector a1 a2
  let w := intVectorToEuclidean c
  let r := A - lambda • w
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hriLe : |r i| <= ‖r‖ := abs_euclideanCoordinate_le_norm r i
  have hrTwoLe : |r 2| <= ‖r‖ := abs_euclideanCoordinate_le_norm r 2
  have hri : |r i| < (X : Real) / 4 := hriLe.trans_lt hresidual
  have hrTwo : |r 2| < (X : Real) / 4 := hrTwoLe.trans_lt hresidual
  have hcoordinateI : r i = A i - lambda * (c i : Real) := by
    rfl
  have hcoordinateTwo : r 2 = (X : Real) - lambda * (c 2 : Real) := by
    simp [r, A, w]
  have haxisTwo : 3 * (X : Real) / 4 <
      |lambda| * |((c 2 : Int) : Real)| := by
    have hsum : (X : Real) = r 2 + lambda * (c 2 : Real) := by
      linarith [hcoordinateTwo]
    have htriangle := abs_add_le (r 2) (lambda * (c 2 : Real))
    rw [<- hsum, abs_of_pos hXReal, abs_mul] at htriangle
    linarith
  have haxisI : |lambda| * |((c i : Int) : Real)| <
      5 * (X : Real) / 4 := by
    have hrewrite : lambda * (c i : Real) = A i - r i := by
      linarith [hcoordinateI]
    have htriangle := abs_sub (A i) (r i)
    rw [<- hrewrite, abs_mul, abs_of_nonneg hiNonneg] at htriangle
    dsimp [A] at hiLt
    linarith
  by_contra hbound
  have hreverse : 2 * |((c 2 : Int) : Real)| <
      |((c i : Int) : Real)| := lt_of_not_ge hbound
  have hlambda : 0 < |lambda| := by
    apply abs_pos.mpr
    intro hlambda
    rw [hlambda, abs_zero, zero_mul] at haxisTwo
    linarith
  have hscaled := mul_lt_mul_of_pos_left hreverse hlambda
  nlinarith

/-- The two-coordinate specialization of the dominant-third-coordinate
estimate. -/
theorem abs_first_coordinates_le_two_mul_third_of_residual_lt
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (c : Fin 3 -> Int) (lambda : Real)
    (hresidual :
      ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <
        (X : Real) / 4) :
    (forall i : Fin 2,
      |((c i.castSucc : Int) : Real)| <= 2 * |((c 2 : Int) : Real)|) := by
  intro i
  apply abs_integerCoordinate_le_two_mul_third_of_residual_lt
    hX a1 a2 c lambda i.castSucc
  · fin_cases i <;> simp
  · fin_cases i
    · simp [latticeAngleVector]
    · simp [latticeAngleVector]
  · exact hresidual

/-- Coordinate ratios differ by at most three times the relative residual
once the third integral coordinate dominates the chosen numerator
coordinate. -/
theorem abs_angleRatio_sub_integerRatio_le_three_mul_residual
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (c : Fin 3 -> Int) (lambda : Real) (i : Fin 3)
    (hcTwo : c 2 ≠ 0)
    (hdominant :
      |((c i : Int) : Real)| <= 2 * |((c 2 : Int) : Real)|) :
    |latticeAngleVector a1 a2 i / (X : Real) -
        ((c i : Int) : Real) / ((c 2 : Int) : Real)| <=
      3 * ‖latticeAngleVector a1 a2 -
        lambda • intVectorToEuclidean c‖ / (X : Real) := by
  let A := latticeAngleVector a1 a2
  let w := intVectorToEuclidean c
  let r := A - lambda • w
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hcTwoReal : ((c 2 : Int) : Real) ≠ 0 := by exact_mod_cast hcTwo
  have hcTwoAbs : 0 < |((c 2 : Int) : Real)| := abs_pos.mpr hcTwoReal
  have hcoordinateI : r i = A i - lambda * (c i : Real) := by
    rfl
  have hcoordinateTwo : r 2 = (X : Real) - lambda * (c 2 : Real) := by
    simp [r, A, w]
  have hidentity :
      A i / (X : Real) - ((c i : Int) : Real) / ((c 2 : Int) : Real) =
        r i / (X : Real) -
          (((c i : Int) : Real) / ((c 2 : Int) : Real)) *
            (r 2 / (X : Real)) := by
    field_simp [hXReal.ne', hcTwoReal]
    rw [hcoordinateI, hcoordinateTwo]
    ring
  have hri : |r i| <= ‖r‖ := abs_euclideanCoordinate_le_norm r i
  have hrTwo : |r 2| <= ‖r‖ := abs_euclideanCoordinate_le_norm r 2
  have hcoordinateRatio :
      |((c i : Int) : Real)| / |((c 2 : Int) : Real)| <= 2 := by
    exact (div_le_iff₀ hcTwoAbs).2 (by simpa using hdominant)
  rw [hidentity]
  calc
    |r i / (X : Real) -
        ((c i : Real) / (c 2 : Real)) * (r 2 / (X : Real))| <=
        |r i / (X : Real)| +
          |((c i : Real) / (c 2 : Real)) * (r 2 / (X : Real))| :=
      abs_sub _ _
    _ = |r i| / (X : Real) +
        (|((c i : Int) : Real)| / |((c 2 : Int) : Real)|) *
          (|r 2| / (X : Real)) := by
      rw [abs_div, abs_mul, abs_div, abs_div, abs_of_pos hXReal]
    _ <= ‖r‖ / (X : Real) + 2 * (‖r‖ / (X : Real)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hri hXReal.le
      · exact mul_le_mul hcoordinateRatio
          (div_le_div_of_nonneg_right hrTwo hXReal.le)
          (by positivity) (by norm_num)
    _ = 3 * ‖r‖ / (X : Real) := by ring

/--
The residual constant `151200` yields the final coordinate error constant `453600` after
natural-denominator normalization.
-/
theorem abs_angleRatio_sub_integerRatio_le_fourHundredFiftyThreeThousandSixHundred
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (N K : Real) (hN : 0 < N) (hK : 0 < K)
    (c : Fin 3 -> Int) (lambda : Real) (i : Fin 3)
    (hcTwo : c 2 ≠ 0)
    (hdominant :
      |((c i : Int) : Real)| <= 2 * |((c 2 : Int) : Real)|)
    (hresidual :
      ‖latticeAngleVector a1 a2 - lambda • intVectorToEuclidean c‖ <=
        151200 * (X : Real) /
          (N * K * ‖intVectorToEuclidean c‖)) :
    |latticeAngleVector a1 a2 i / (X : Real) -
        ((c i : Int) : Real) / ((c 2 : Int) : Real)| <=
      453600 / (N * K * (integerVectorDenominator c : Real)) := by
  let w := intVectorToEuclidean c
  let r := latticeAngleVector a1 a2 - lambda • w
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hc : c ≠ 0 := by
    intro hzero
    apply hcTwo
    exact congrFun hzero 2
  have hw : w ≠ 0 := by
    simpa [w] using intVectorToEuclidean_injective.ne hc
  have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hcTwoReal : ((c 2 : Int) : Real) ≠ 0 := by exact_mod_cast hcTwo
  have hcTwoAbs : 0 < |((c 2 : Int) : Real)| := abs_pos.mpr hcTwoReal
  have hcoordinate : |((c 2 : Int) : Real)| <= ‖w‖ := by
    simpa [w, Real.norm_eq_abs] using PiLp.norm_apply_le w 2
  have hratio := abs_angleRatio_sub_integerRatio_le_three_mul_residual
    hX a1 a2 c lambda i hcTwo hdominant
  calc
    |latticeAngleVector a1 a2 i / (X : Real) -
        ((c i : Int) : Real) / ((c 2 : Int) : Real)| <=
        3 * ‖r‖ / (X : Real) := by
      simpa [r, w] using hratio
    _ <= 3 * (151200 * (X : Real) / (N * K * ‖w‖)) /
        (X : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa [r, w] using hresidual)
          (by norm_num)) hXReal.le
    _ = 453600 / (N * K * ‖w‖) := by
      field_simp [hXReal.ne', hN.ne', hK.ne', hwNorm.ne']
      norm_num
    _ <= 453600 /
        (N * K * |((c 2 : Int) : Real)|) := by
      apply div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (mul_pos hN hK) hcTwoAbs)
      exact mul_le_mul_of_nonneg_left hcoordinate (mul_pos hN hK).le
    _ = 453600 /
        (N * K * (integerVectorDenominator c : Real)) := by
      rw [cast_integerVectorDenominator]

/--
In the large-product branch, the residual bound is strictly smaller than `X/4`. The lower norm
bound is arithmetic integrality, not an asymptotic assertion.
-/
theorem residual_lt_quarter_of_million_lt_product
    {X : Nat} (hX : 0 < X) (N K : Real)
    (c : Fin 3 -> Int) (hc : c ≠ 0) (r : E)
    (hlarge : 1000000 < N * K)
    (hresidual : ‖r‖ <=
      151200 * (X : Real) / (N * K * ‖intVectorToEuclidean c‖)) :
    ‖r‖ < (X : Real) / 4 := by
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hproduct : 0 < N * K := lt_trans (by norm_num) hlarge
  have hnorm : 1 <= ‖intVectorToEuclidean c‖ :=
    one_le_norm_intVectorToEuclidean hc
  have hdenominator : N * K <= N * K * ‖intVectorToEuclidean c‖ := by
    nlinarith
  have hfirst : 151200 * (X : Real) /
      (N * K * ‖intVectorToEuclidean c‖) <=
        151200 * (X : Real) / (N * K) := by
    exact div_le_div_of_nonneg_left (by positivity) hproduct hdenominator
  have hscale := mul_lt_mul_of_pos_left hlarge hXReal
  have hsecond : 151200 * (X : Real) / (N * K) < (X : Real) / 4 := by
    apply (div_lt_iff₀ hproduct).2
    nlinarith
  exact hresidual.trans_lt (hfirst.trans_lt hsecond)

/-- For `N*K` at most the final absolute constant, denominator one and zero
numerators already give the required simultaneous approximation. -/
theorem exists_trivial_latticeSimultaneousApproximation
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (N K : Real) (hN : 0 < N) (hK : 0 < K)
    (hproduct : N * K <= 1000000) :
    exists q : Nat, 0 < q ∧
      (q : Real) <= 1000000 * (X : Real) / (N * K) ∧
      exists b1 b2 : Int,
        |(((a1 : Nat) : Real) / (X : Real) -
          (b1 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) ∧
        |(((a2 : Nat) : Real) / (X : Real) -
          (b2 : Real) / (q : Real))| <=
            1000000 / (N * K * (q : Real)) := by
  have hXOne : (1 : Real) <= X := by exact_mod_cast hX
  have hproductPos : 0 < N * K := mul_pos hN hK
  have hqBound : (1 : Real) <= 1000000 * (X : Real) / (N * K) := by
    apply (le_div_iff₀ hproductPos).2
    nlinarith
  have hone : (1 : Real) <= 1000000 / (N * K) := by
    apply (le_div_iff₀ hproductPos).2
    simpa using hproduct
  have hangle (a : Fin X) :
      |(((a : Nat) : Real) / (X : Real))| <= 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast a.isLt.le)
  refine ⟨1, by norm_num, ?_, 0, 0, ?_, ?_⟩
  · simpa using hqBound
  · simpa using (hangle a1).trans hone
  · simpa using (hangle a2).trans hone

end PrimesRestrictedDigits
