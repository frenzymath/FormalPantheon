import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearIntervals
import PrimesRestrictedDigits.Fourier.LInfLocal
import PrimesRestrictedDigits.LatticeEstimates.AngleVector
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Integral relation points from close bilinear pairs

The sign involution is built into the point `(n1, -n2, -k)`. Consequently all later geometry
uses the project's standard all-plus angle vector `(a1, a2, X)`.
-/

namespace PrimesRestrictedDigits

/-- The signed normalized linear form attached to a frequency pair and two
natural variables. -/
noncomputable def bilinearRelationPhase {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) : Real :=
  (((a1 : Nat) : Real) * n1 - ((a2 : Nat) : Real) * n2) / (X : Real)

/-- The nearest-integer relation point attached to a natural pair. -/
noncomputable def bilinearRelationPoint {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) : Fin 3 -> Int :=
  ![(n1 : Int), -(n2 : Int),
    -round (bilinearRelationPhase a1 a2 n1 n2)]

@[simp]
theorem bilinearRelationPoint_apply_zero {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) :
    bilinearRelationPoint a1 a2 n1 n2 0 = n1 :=
  rfl

@[simp]
theorem bilinearRelationPoint_apply_one {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) :
    bilinearRelationPoint a1 a2 n1 n2 1 = -(n2 : Int) :=
  rfl

@[simp]
theorem bilinearRelationPoint_apply_two {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) :
    bilinearRelationPoint a1 a2 n1 n2 2 =
      -round ((((a1 : Nat) : Real) * n1 -
        ((a2 : Nat) : Real) * n2) / (X : Real)) :=
  rfl

/-- The relation-point map is injective in the two natural coordinates. -/
theorem bilinearRelationPoint_injective {X : Nat} (a1 a2 : Fin X) :
    Function.Injective fun p : Nat × Nat =>
      bilinearRelationPoint a1 a2 p.1 p.2 := by
  intro p q hpq
  apply Prod.ext
  · have hzero := congrFun hpq 0
    simpa using hzero
  · have hone := congrFun hpq 1
    simpa using hone

/-- The all-plus integral dot product is exactly the signed source residual. -/
theorem intVectorDot_bilinearRelationPoint {X : Nat}
    (a1 a2 : Fin X) (n1 n2 : Nat) :
    ((intVectorDot (bilinearRelationPoint a1 a2 n1 n2)
        (angleCoefficientVector a1 a2) : Int) : Real) =
      (((a1 : Nat) : Real) * n1 - ((a2 : Nat) : Real) * n2) -
        (X : Real) *
          round ((((a1 : Nat) : Real) * n1 -
            ((a2 : Nat) : Real) * n2) / (X : Real)) := by
  simp only [intVectorDot, Fin.sum_univ_three,
    bilinearRelationPoint_apply_zero, bilinearRelationPoint_apply_one,
    bilinearRelationPoint_apply_two, angleCoefficientVector_zero,
    angleCoefficientVector_one, angleCoefficientVector_two]
  push_cast
  ring

/-- The residual dot product has size `X` times the nearest-integer distance. -/
theorem abs_intVectorDot_bilinearRelationPoint {X : Nat}
    (hX : 0 < X) (a1 a2 : Fin X) (n1 n2 : Nat) :
    |((intVectorDot (bilinearRelationPoint a1 a2 n1 n2)
        (angleCoefficientVector a1 a2) : Int) : Real)| =
      (X : Real) * nearestIntegerDistance
        ((((a1 : Nat) : Real) * n1 -
          ((a2 : Nat) : Real) * n2) / (X : Real)) := by
  let u : Real := ((a1 : Nat) : Real) * n1 -
    ((a2 : Nat) : Real) * n2
  have hXReal : (0 : Real) < X := by exact_mod_cast hX
  rw [intVectorDot_bilinearRelationPoint, nearestIntegerDistance]
  change |u - (X : Real) * (round (u / X) : Int)| =
    (X : Real) * |u / X - (round (u / X) : Int)|
  have hfactor :
      u - (X : Real) * (round (u / X) : Int) =
        (X : Real) * (u / X - (round (u / X) : Int)) := by
    field_simp
  rw [hfactor, abs_mul, abs_of_pos hXReal]

private theorem abs_bilinearPhaseNumerator_div_le_two_mul
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    {n1 n2 : Nat} {N : Real}
    (hn1 : (n1 : Real) <= N) (hn2 : (n2 : Real) <= N) :
    |((((a1 : Nat) : Real) * n1 -
        ((a2 : Nat) : Real) * n2) / (X : Real))| <= 2 * N := by
  have hXReal : (0 : Real) < X := by exact_mod_cast hX
  have ha1 : (((a1 : Nat) : Real)) <= X := by
    exact_mod_cast a1.isLt.le
  have ha2 : (((a2 : Nat) : Real)) <= X := by
    exact_mod_cast a2.isLt.le
  have hn1Nonneg : (0 : Real) <= n1 := by positivity
  have hn2Nonneg : (0 : Real) <= n2 := by positivity
  have hNNonneg : 0 <= N := hn1Nonneg.trans hn1
  have hterm1Nonneg :
      0 <= ((a1 : Nat) : Real) * n1 := mul_nonneg (by positivity) hn1Nonneg
  have hterm2Nonneg :
      0 <= ((a2 : Nat) : Real) * n2 := mul_nonneg (by positivity) hn2Nonneg
  rw [abs_div, abs_of_pos hXReal]
  apply (div_le_iff₀ hXReal).2
  calc
    |((a1 : Nat) : Real) * n1 - ((a2 : Nat) : Real) * n2| <=
        ((a1 : Nat) : Real) * n1 + ((a2 : Nat) : Real) * n2 := by
      rw [abs_le]
      constructor <;> linarith
    _ <= (X : Real) * N + (X : Real) * N := by
      gcongr
    _ = 2 * N * (X : Real) := by ring

private theorem abs_round_bilinearPhase_le_three_mul
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    {n1 n2 : Nat} {N : Real} (hN : 1 <= N)
    (hn1 : (n1 : Real) <= N) (hn2 : (n2 : Real) <= N) :
    |((round ((((a1 : Nat) : Real) * n1 -
        ((a2 : Nat) : Real) * n2) / (X : Real)) : Int) : Real)| <= 3 * N := by
  let x : Real := (((a1 : Nat) : Real) * n1 -
    ((a2 : Nat) : Real) * n2) / (X : Real)
  have hx := abs_bilinearPhaseNumerator_div_le_two_mul
    hX a1 a2 hn1 hn2
  have hround : |((round x : Int) : Real)| <= |x| + 1 / 2 := by
    calc
      |((round x : Int) : Real)| = |x - (x - (round x : Int))| := by
        congr 1
        ring
      _ <= |x| + |x - (round x : Int)| := abs_sub _ _
      _ <= |x| + 1 / 2 := by gcongr; exact abs_sub_round x
  calc
    |((round x : Int) : Real)| <= |x| + 1 / 2 := hround
    _ <= 2 * N + 1 / 2 := by
      dsimp only [x] at hx ⊢
      gcongr
    _ <= 3 * N := by linarith

/-- Source-range natural pairs map to integral vectors of norm at most `10N`.
The deliberately loose constant keeps the bridge stable at `N=1`. -/
theorem norm_bilinearRelationPoint_le_ten_mul
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    {n1 n2 : Nat} {N : Real} (hN : 1 <= N)
    (hn1 : (n1 : Real) <= N) (hn2 : (n2 : Real) <= N) :
    ‖intVectorToEuclidean (bilinearRelationPoint a1 a2 n1 n2)‖ <=
      10 * N := by
  have hn1sq : (n1 : Real) ^ 2 <= N ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (zero_le_one.trans hN)).2 hn1
  have hn2sq : (n2 : Real) ^ 2 <= N ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (zero_le_one.trans hN)).2 hn2
  have hround := abs_round_bilinearPhase_le_three_mul
    hX a1 a2 hN hn1 hn2
  have hroundSq :
      (((round ((((a1 : Nat) : Real) * n1 -
          ((a2 : Nat) : Real) * n2) / (X : Real)) : Int) : Real)) ^ 2 <=
        (3 * N) ^ 2 := by
    have habsSq := (sq_le_sq₀ (abs_nonneg
      (((round ((((a1 : Nat) : Real) * n1 -
        ((a2 : Nat) : Real) * n2) / (X : Real)) : Int) : Real)))
      (by positivity : 0 <= 3 * N)).2 hround
    simpa only [sq_abs] using habsSq
  have hnormSq :
      ‖intVectorToEuclidean (bilinearRelationPoint a1 a2 n1 n2)‖ ^ 2 <=
        (10 * N) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp only [intVectorToEuclidean_apply,
      bilinearRelationPoint_apply_zero, bilinearRelationPoint_apply_one,
      bilinearRelationPoint_apply_two, Int.cast_natCast, Int.cast_neg]
    nlinarith [sq_nonneg N]
  nlinarith [norm_nonneg
    (intVectorToEuclidean (bilinearRelationPoint a1 a2 n1 n2))]

/-- Pairs in the exact source interval whose phase distance is at most
`delta`. -/
noncomputable def bilinearCloseNaturalPairs {X : Nat}
    (a1 a2 : Fin X) (N delta : Real) : Finset (Nat × Nat) := by
  classical
  exact ((sourceFactorTenNaturalInterval N).product
    (sourceFactorTenNaturalInterval N)).filter fun p =>
      nearestIntegerDistance
        (bilinearRelationPhase a1 a2 p.1 p.2) <= delta

@[simp]
theorem mem_bilinearCloseNaturalPairs_iff {X : Nat}
    {a1 a2 : Fin X} {N delta : Real} {p : Nat × Nat} :
    p ∈ bilinearCloseNaturalPairs a1 a2 N delta ↔
      p.1 ∈ sourceFactorTenNaturalInterval N ∧
      p.2 ∈ sourceFactorTenNaturalInterval N ∧
      nearestIntegerDistance
        (bilinearRelationPhase a1 a2 p.1 p.2) <= delta := by
  simp [bilinearCloseNaturalPairs, and_assoc]

/-- The finite integral carrier produced from the close natural pairs. -/
noncomputable def bilinearRelationPoints {X : Nat}
    (a1 a2 : Fin X) (N delta : Real) : Finset (Fin 3 -> Int) := by
  classical
  exact (bilinearCloseNaturalPairs a1 a2 N delta).image fun p =>
    bilinearRelationPoint a1 a2 p.1 p.2

theorem card_bilinearRelationPoints {X : Nat}
    (a1 a2 : Fin X) (N delta : Real) :
    (bilinearRelationPoints a1 a2 N delta).card =
      (bilinearCloseNaturalPairs a1 a2 N delta).card := by
  classical
  exact Finset.card_image_of_injective _
    (bilinearRelationPoint_injective a1 a2)

/-- Every retained relation point obeys the norm and all-plus dot bounds
needed by the geometry split. -/
theorem bilinearRelationPoints_bounds {X : Nat}
    (hX : 0 < X) (a1 a2 : Fin X) {N delta : Real}
    (hN : 1 <= N) (_hdelta : 0 <= delta)
    {z : Fin 3 -> Int} (hz : z ∈ bilinearRelationPoints a1 a2 N delta) :
    ‖intVectorToEuclidean z‖ <= 10 * N ∧
      |((intVectorDot z (angleCoefficientVector a1 a2) : Int) : Real)| <=
        delta * (X : Real) := by
  classical
  rw [bilinearRelationPoints, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hpData := mem_bilinearCloseNaturalPairs_iff.mp hp
  have hp1 := (mem_sourceFactorTenNaturalInterval_iff
    (zero_le_one.trans hN)).mp hpData.1
  have hp2 := (mem_sourceFactorTenNaturalInterval_iff
    (zero_le_one.trans hN)).mp hpData.2.1
  constructor
  · exact norm_bilinearRelationPoint_le_ten_mul
      hX a1 a2 hN hp1.2 hp2.2
  · rw [abs_intVectorDot_bilinearRelationPoint hX]
    have hXNonneg : (0 : Real) <= (X : Real) := by positivity
    simpa only [bilinearRelationPhase, mul_comm] using
      (mul_le_mul_of_nonneg_left hpData.2.2 hXNonneg)

end PrimesRestrictedDigits
