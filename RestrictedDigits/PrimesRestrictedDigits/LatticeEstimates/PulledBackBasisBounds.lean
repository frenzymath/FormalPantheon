import PrimesRestrictedDigits.LatticeEstimates.ReducedImageBasisBounds
import Mathlib.Tactic.FieldSimp

/-!
# Pulling the reduced image basis back to the integral lattice

This supplies the repaired inverse-dilation factor in `MAYNARD-PRD-PUBLISHED`, Lemma 14.1. The
paper's claim that dilation only increases norms is false without an additional hypothesis.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The canonical cube bound forces `delta<=27*N` over the literal source
range. -/
theorem delta_le_twenty_seven_mul_of_generatingPoints
    {X : Nat} (a1 a2 : Fin X) (delta N K : Real)
    (hdelta : 0 < delta) (hN : 1 <= N) (hK : 1 <= K)
    (Lambda : RankTwoIntegralLattice)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real)) :
    delta <= 27 * N := by
  let S := latticeGeneratingIntegerPoints a1 a2 Lambda delta N
  have hSnorm : forall z, z ∈ S -> ‖intVectorToEuclidean z‖ <= N := by
    intro z hz
    exact ((mem_latticeGeneratingIntegerPoints (zero_le_one.trans hN)).mp hz).2.1
  have hcube : (S.card : Real) <= 27 * N ^ 3 :=
    card_real_le_twenty_seven_mul_cube S N hN hSnorm
  have hdeltaK : delta <= delta * K := by
    calc
      delta = delta * 1 := by ring
      _ <= delta * K := mul_le_mul_of_nonneg_left hK hdelta.le
  have hscaled : delta * N ^ 2 <= delta * K * N ^ 2 := by
    exact mul_le_mul_of_nonneg_right hdeltaK (sq_nonneg N)
  have hbound : delta * N ^ 2 <= 27 * N ^ 3 := by
    exact hscaled.trans (hcard.trans hcube)
  have hcancel : delta * N ^ 2 <= (27 * N) * N ^ 2 := by
    convert hbound using 1; ring
  exact le_of_mul_le_mul_right hcancel (sq_pos_of_pos (zero_lt_one.trans_le hN))

/-- The inverse directional dilation has norm at most `28` on every vector
under the repaired source hypotheses. -/
theorem norm_sourceDirectionalDilation_symm_le_twenty_eight
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N : Real) (hdelta : 0 < delta) (hN : 0 < N)
    (hdeltaN : delta <= 27 * N) (v : E) :
    ‖(directionalDilation (latticeAngleVector a1 a2) (N / delta)
        (latticeAngleVector_ne_zero hX a1 a2)
        (div_ne_zero hN.ne' hdelta.ne')).symm v‖ <= 28 * ‖v‖ := by
  let A := latticeAngleVector a1 a2
  let hA : A ≠ 0 := latticeAngleVector_ne_zero hX a1 a2
  let t := N / delta
  let ht : t ≠ 0 := div_ne_zero hN.ne' hdelta.ne'
  have htpos : 0 < t := div_pos hN hdelta
  have hinv : t⁻¹ = delta / N := by
    dsimp [t]
    field_simp [hN.ne', hdelta.ne']
  have hratio : delta / N <= 27 :=
    (div_le_iff₀ hN).2 (by simpa using hdeltaN)
  calc
    ‖(directionalDilation A t hA ht).symm v‖ <=
        ‖v‖ + t⁻¹ * ‖lineProjection A v‖ :=
      norm_directionalDilation_symm_le A t hA htpos v
    _ <= ‖v‖ + t⁻¹ * ‖v‖ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_lineProjection_le A v) (inv_nonneg.mpr htpos.le))
    _ = ‖v‖ + (delta / N) * ‖v‖ := by rw [hinv]
    _ <= 28 * ‖v‖ := by
      nlinarith [norm_nonneg v]

/-- Pull one image-basis vector back to the original integral lattice. -/
def pulledBackBasisVector
    (Lambda : RankTwoIntegralLattice) (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0)
    (b : Module.Basis (Fin 2) Int
      (directionallyDilatedLattice Lambda u t hu ht)) (i : Fin 2) :
    Lambda.carrier :=
  (directionallyDilatedLatticeEquiv Lambda u t hu ht).symm (b i)

@[simp] theorem pulledBackBasisVector_coe
    (Lambda : RankTwoIntegralLattice) (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0)
    (b : Module.Basis (Fin 2) Int
      (directionallyDilatedLattice Lambda u t hu ht)) (i : Fin 2) :
    (pulledBackBasisVector Lambda u t hu ht b i : E) =
      (directionalDilation u t hu ht).symm (b i : E) :=
  by
    apply (directionalDilation u t hu ht).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := congrArg Subtype.val
      ((directionallyDilatedLatticeEquiv Lambda u t hu ht).apply_symm_apply (b i))
    change
      ((directionallyDilatedLatticeEquiv Lambda u t hu ht
        ((directionallyDilatedLatticeEquiv Lambda u t hu ht).symm (b i)) :
          directionallyDilatedLattice Lambda u t hu ht) : E) = (b i : E) at h
    rw [directionallyDilatedLatticeEquiv_coe] at h
    exact h

theorem norm_pulledBackBasisVector_le
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N : Real) (hdelta : 0 < delta) (hN : 0 < N)
    (hdeltaN : delta <= 27 * N) (Lambda : RankTwoIntegralLattice)
    (b : Module.Basis (Fin 2) Int
      (directionallyDilatedLattice Lambda (latticeAngleVector a1 a2)
        (N / delta) (latticeAngleVector_ne_zero hX a1 a2)
        (div_ne_zero hN.ne' hdelta.ne'))) (i : Fin 2) :
    ‖(pulledBackBasisVector Lambda (latticeAngleVector a1 a2) (N / delta)
      (latticeAngleVector_ne_zero hX a1 a2)
      (div_ne_zero hN.ne' hdelta.ne') b i : E)‖ <=
        28 * ‖(b i : E)‖ := by
  rw [pulledBackBasisVector_coe]
  exact norm_sourceDirectionalDilation_symm_le_twenty_eight
    hX a1 a2 delta N hdelta hN hdeltaN (b i : E)

/-- The pulled-back basis vector has the required small scalar product with
the angle vector. -/
theorem abs_inner_pulledBackBasisVector_le
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N : Real) (hdelta : 0 < delta) (hN : 0 < N)
    (Lambda : RankTwoIntegralLattice)
    (b : Module.Basis (Fin 2) Int
      (directionallyDilatedLattice Lambda (latticeAngleVector a1 a2)
        (N / delta) (latticeAngleVector_ne_zero hX a1 a2)
        (div_ne_zero hN.ne' hdelta.ne'))) (i : Fin 2) :
    |inner Real (latticeAngleVector a1 a2)
      (pulledBackBasisVector Lambda (latticeAngleVector a1 a2) (N / delta)
        (latticeAngleVector_ne_zero hX a1 a2)
        (div_ne_zero hN.ne' hdelta.ne') b i : E)| <=
      3 * delta * (X : Real) * ‖(b i : E)‖ / N := by
  let A := latticeAngleVector a1 a2
  let hA : A ≠ 0 := latticeAngleVector_ne_zero hX a1 a2
  let t := N / delta
  let ht : t ≠ 0 := div_ne_zero hN.ne' hdelta.ne'
  have hinv : t⁻¹ = delta / N := by
    dsimp [t]
    field_simp [hN.ne', hdelta.ne']
  rw [pulledBackBasisVector_coe, inner_directionalDilation_symm, hinv,
    abs_mul, abs_of_pos (div_pos hdelta hN)]
  have hratio : 0 <= delta / N := (div_pos hdelta hN).le
  calc
    delta / N * |inner Real A (b i : E)| <=
        delta / N * (‖A‖ * ‖(b i : E)‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm A (b i : E)) hratio
    _ <= delta / N * ((3 * (X : Real)) * ‖(b i : E)‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (norm_latticeAngleVector_le_three_mul hX a1 a2)
          (norm_nonneg (b i : E))) hratio
    _ = 3 * delta * (X : Real) * ‖(b i : E)‖ / N := by
      field_simp [hN.ne']

end PrimesRestrictedDigits
