import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearRelationPoints
import PrimesRestrictedDigits.ExceptionalMinorArcs.GeometryOfNumbers
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineGeneratingPairs
import PrimesRestrictedDigits.LatticeEstimates.GeneratingPairs
import Mathlib.Tactic.Push

/-!
# Geometry split for rich bilinear relations

This is the normalized, sign-corrected bridge omitted in the published proof of Lemma 13.1. A
rich relation carrier makes its frequency pair either a Proposition 13.3 lattice-generating
pair or a Proposition 13.4 line-generating pair at parameters `(10N, 10delta, K'/2000)`.
-/

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- A rich close-pair carrier enters one of the two existing structured
frequency-pair carriers. -/
theorem latticeGenerating_or_lineGenerating_of_relationPoints
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    {N delta K' : Real} (hN : 1 <= N) (hdelta : 0 < delta)
    (hKLarge : 100 * geometryOfNumbersK0 <= K')
    (hcard : delta * K' * N ^ 2 <=
      ((bilinearRelationPoints a1 a2 N delta).card : Real)) :
    (a1, a2) ∈
        latticeGeneratingPairs (10 * N) (K' / 2000) (10 * delta) ∨
      IsLineGeneratingPair
        (10 * delta) (10 * N) (K' / 2000) a1 a2 := by
  classical
  let A : E := latticeAngleVector a1 a2
  let R : Real := ‖A‖
  let t : E := R⁻¹ • A
  let Ng : Real := 10 * N
  let deltag : Real := delta * (X : Real) / R
  let Kg : Real := K' * R / (100 * (X : Real))
  let S := bilinearRelationPoints a1 a2 N delta
  let Np : Real := 10 * N
  let deltap : Real := 10 * delta
  let Kp : Real := K' / 2000
  have hXReal : (0 : Real) < X := by exact_mod_cast hX
  have hAPos : 0 < ‖A‖ := norm_pos_iff.mpr
    (latticeAngleVector_ne_zero hX a1 a2)
  have hR : 0 < R := hAPos
  have hRLower : (X : Real) <= R :=
    cast_le_norm_latticeAngleVector a1 a2
  have hK' : 0 < K' := by
    have hK0 : 0 < geometryOfNumbersK0 := by
      norm_num [geometryOfNumbersK0]
    nlinarith
  have ht : ‖t‖ = 1 := by
    exact norm_smul_inv_norm (latticeAngleVector_ne_zero hX a1 a2)
  have hNg : 0 < Ng := by dsimp only [Ng]; positivity
  have hdeltag : 0 < deltag := by dsimp only [deltag]; positivity
  have hKg : geometryOfNumbersK0 <= Kg := by
    have hfirst : geometryOfNumbersK0 <= K' / 100 := by
      nlinarith
    have hratio : 1 <= R / (X : Real) :=
      (le_div_iff₀ hXReal).2 (by simpa only [one_mul] using hRLower)
    have hnonneg : 0 <= K' / 100 := by positivity
    calc
      geometryOfNumbersK0 <= K' / 100 := hfirst
      _ <= (K' / 100) * (R / (X : Real)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hnonneg
      _ = Kg := by
        dsimp only [Kg]
        field_simp
  have hnormalized :
      deltag * Kg * Ng ^ 2 = delta * K' * N ^ 2 := by
    dsimp only [deltag, Kg, Ng]
    field_simp [hR.ne', hXReal.ne']
    ring
  have hSbounds : ∀ z ∈ S,
      ‖intVectorToEuclidean z‖ <= Ng ∧
        abs (inner Real t (intVectorToEuclidean z)) <= deltag := by
    intro z hz
    have hzBounds := bilinearRelationPoints_bounds
      hX a1 a2 hN hdelta.le hz
    constructor
    · simpa only [Ng] using hzBounds.1
    · have hdot :
          |inner Real A (intVectorToEuclidean z)| <=
            delta * (X : Real) := by
        rw [real_inner_comm]
        simpa only [A, intVectorDot_angle_cast_eq_inner] using hzBounds.2
      have hscaled := mul_le_mul_of_nonneg_left hdot (inv_nonneg.mpr hR.le)
      simpa only [t, deltag, real_inner_smul_left, abs_mul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hScard : deltag * Kg * Ng ^ 2 <= (S.card : Real) := by
    rw [hnormalized]
    exact hcard
  obtain ⟨Lambda, hLambda⟩ :=
    exists_rankTwoIntegralLattice_geometryOfNumbers
      t Ng deltag Kg ht hNg hdeltag hKg S hSbounds hScard
  let G := latticeGeneratingIntegerPoints a1 a2 Lambda deltap Np
  have hSsubG : S ⊆ G := by
    intro z hz
    have hzBounds := bilinearRelationPoints_bounds
      hX a1 a2 hN hdelta.le hz
    apply (mem_latticeGeneratingIntegerPoints hNg.le).mpr
    refine ⟨hLambda z hz, hzBounds.1, ?_⟩
    have hwide : delta * (X : Real) <= deltap * (X : Real) := by
      dsimp only [deltap]
      gcongr
      linarith
    exact hzBounds.2.trans hwide
  have hparameter :
      deltap * Kp * Np ^ 2 = delta * K' * N ^ 2 / 2 := by
    dsimp only [deltap, Kp, Np]
    ring
  have hrequired : deltap * Kp * Np ^ 2 <= (S.card : Real) := by
    rw [hparameter]
    have hproductNonneg : 0 <= delta * K' * N ^ 2 := by positivity
    exact (div_le_self hproductNonneg (by norm_num)).trans hcard
  have hGcard : deltap * Kp * Np ^ 2 <= (G.card : Real) := by
    exact hrequired.trans (by
      exact_mod_cast Finset.card_le_card hSsubG)
  by_cases hnonlinear : LatticePointsNotContainedInLine G
  · left
    apply mem_latticeGeneratingPairs_iff.mpr
    exact ⟨Lambda, hGcard, hnonlinear⟩
  · right
    unfold LatticePointsNotContainedInLine at hnonlinear
    push Not at hnonlinear
    obtain ⟨line, hline, hcontained⟩ := hnonlinear
    refine ⟨line, hline, ?_⟩
    let H := lineGeneratingIntegerPoints a1 a2 line deltap Np
    have hSsubH : S ⊆ H := by
      intro z hz
      have hzBounds := bilinearRelationPoints_bounds
        hX a1 a2 hN hdelta.le hz
      apply (mem_lineGeneratingIntegerPoints hNg.le).mpr
      refine ⟨hcontained z (hSsubG hz), hzBounds.1, ?_⟩
      have hwide : delta * (X : Real) <= deltap * (X : Real) := by
        dsimp only [deltap]
        gcongr
        linarith
      exact hzBounds.2.trans hwide
    change deltap * Np ^ 2 * Kp <= (H.card : Real)
    calc
      deltap * Np ^ 2 * Kp = deltap * Kp * Np ^ 2 := by ring
      _ <= (S.card : Real) := hrequired
      _ <= (H.card : Real) := by
        exact_mod_cast Finset.card_le_card hSsubH

end PrimesRestrictedDigits
