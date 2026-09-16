import PrimesRestrictedDigits.LatticeEstimates.ReducedImageBasis
import Mathlib.Tactic.FinCases

/-!
# Quantitative bounds for the reduced image basis

This proves the explicit `900/(delta*K)` basis-norm product bound in the
repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

private theorem one_le_cast_abs_of_ne_zero {z : Int} (hz : z ≠ 0) :
    (1 : Real) <= ((|z| : Int) : Real) := by
  have hnat : 1 <= z.natAbs := Int.natAbs_pos.mpr hz
  have hreal : (1 : Real) <= (z.natAbs : Real) := by
    exact_mod_cast hnat
  simpa [Nat.cast_natAbs, Int.cast_abs] using hreal

/-- The dilated image lattice has a sorted integral basis whose two norms are
at most `6*N` and whose norm product is at most `900/(delta*K)`. -/
theorem exists_directionallyDilatedBasis_with_bounds
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N K : Real) (hdelta : 0 < delta) (hN : 0 < N) (hK : 0 < K)
    (Lambda : RankTwoIntegralLattice)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists b : Module.Basis (Fin 2) Int
        (directionallyDilatedLattice Lambda (latticeAngleVector a1 a2)
          (N / delta) (latticeAngleVector_ne_zero hX a1 a2)
          (div_ne_zero hN.ne' hdelta.ne')),
      (forall i, 0 < ‖(b i : E)‖) ∧
      (forall i, ‖(b i : E)‖ <= 6 * N) ∧
      ‖(b 0 : E)‖ * ‖(b 1 : E)‖ <= 900 / (delta * K) := by
  let A := latticeAngleVector a1 a2
  let hA : A ≠ 0 := latticeAngleVector_ne_zero hX a1 a2
  let t := N / delta
  let ht : t ≠ 0 := div_ne_zero hN.ne' hdelta.ne'
  let S := latticeGeneratingIntegerPoints a1 a2 Lambda delta N
  have hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier := by
    intro z hz
    exact ((mem_latticeGeneratingIntegerPoints hN.le).mp hz).1
  let L := directionallyDilatedLattice Lambda A t hA ht
  let T := dilatedPointSet Lambda S hS A t hA ht
  obtain ⟨b, hmono, hweighted⟩ :=
    exists_sortedBasis_directionallyDilatedLattice Lambda A t hA ht
  let V : Fin 2 -> Real := fun i => ‖(b i : E)‖
  have hVpos : forall i, 0 < V i := by
    intro i
    apply norm_pos_iff.mpr
    intro hzero
    exact b.ne_zero i (Subtype.ext hzero)
  have hTnorm : forall x, x ∈ T -> ‖(x : E)‖ <= 2 * N := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ :=
      exists_of_mem_dilatedPointSet Lambda S hS A t hA ht hx
    change ‖directionalDilation A t hA ht (intVectorToEuclidean z)‖ <= 2 * N
    exact norm_directionalDilation_generatingPoint_le
      hX a1 a2 delta N hdelta hN Lambda hz
  have hcoord : forall x, x ∈ T -> forall i,
      ((|b.repr x i| : Int) : Real) * V i <= 6 * N := by
    intro x hx i
    exact basis_repr_mul_norm_le_six L b hweighted N x (hTnorm x hx) i
  obtain ⟨z, hz, w, hw, hzw⟩ :=
    (latticePointsNotContainedInLine_iff_exists_linearIndependent S).mp
      hnonlinear
  let x : L := directionallyDilatedLatticeEquiv Lambda A t hA ht
    ⟨intVectorToEuclidean z, hS z hz⟩
  let y : L := directionallyDilatedLatticeEquiv Lambda A t hA ht
    ⟨intVectorToEuclidean w, hS w hw⟩
  have hx : x ∈ T :=
    dilatedPoint_mem_dilatedPointSet Lambda S hS A t hA ht hz
  have hy : y ∈ T :=
    dilatedPoint_mem_dilatedPointSet Lambda S hS A t hA ht hw
  have hxy : LinearIndependent Real ![(x : E), (y : E)] := by
    have hmapped := hzw.map'
      (directionalDilation A t hA ht).toLinearMap
      (by simp)
    have heq :
        (directionalDilation A t hA ht).toLinearMap ∘
            ![intVectorToEuclidean z, intVectorToEuclidean w] =
          ![directionalDilation A t hA ht (intVectorToEuclidean z),
            directionalDilation A t hA ht (intVectorToEuclidean w)] := by
      funext i
      fin_cases i <;> rfl
    rw [heq] at hmapped
    simpa [x, y] using hmapped
  have hrepr : b.repr x 1 ≠ 0 ∨ b.repr y 1 ≠ 0 :=
    repr_one_ne_zero_of_linearIndependent L b hxy
  have hV1 : V 1 <= 6 * N := by
    rcases hrepr with hxrepr | hyrepr
    · calc
        V 1 = 1 * V 1 := by ring
        _ <= ((|b.repr x 1| : Int) : Real) * V 1 :=
          mul_le_mul_of_nonneg_right
            (one_le_cast_abs_of_ne_zero hxrepr) (hVpos 1).le
        _ <= 6 * N := hcoord x hx 1
    · calc
        V 1 = 1 * V 1 := by ring
        _ <= ((|b.repr y 1| : Int) : Real) * V 1 :=
          mul_le_mul_of_nonneg_right
            (one_le_cast_abs_of_ne_zero hyrepr) (hVpos 1).le
        _ <= 6 * N := hcoord y hy 1
  have hV0 : V 0 <= 6 * N := by
    exact (hmono (by decide : (0 : Fin 2) <= 1)).trans hV1
  have hVbound : forall i, V i <= 6 * N := by
    intro i
    fin_cases i
    · exact hV0
    · exact hV1
  have hcount : (T.card : Real) * (V 0 * V 1) <= 900 * N ^ 2 :=
    card_mul_basis_norms_le_nine_hundred b T V N hVpos hVbound hcoord
  have hcardT : delta * K * N ^ 2 <= (T.card : Real) := by
    simpa [T, S] using hcard
  have hVnonneg : 0 <= V 0 * V 1 :=
    mul_nonneg (hVpos 0).le (hVpos 1).le
  have hscaled := mul_le_mul_of_nonneg_right hcardT hVnonneg
  have hcancel : (delta * K * (V 0 * V 1)) * N ^ 2 <=
      900 * N ^ 2 := by
    calc
      (delta * K * (V 0 * V 1)) * N ^ 2 =
          (delta * K * N ^ 2) * (V 0 * V 1) := by ring
      _ <= (T.card : Real) * (V 0 * V 1) := hscaled
      _ <= 900 * N ^ 2 := hcount
  have hproductMul : delta * K * (V 0 * V 1) <= 900 := by
    exact le_of_mul_le_mul_right hcancel (sq_pos_of_pos hN)
  have hproduct : V 0 * V 1 <= 900 / (delta * K) := by
    apply (le_div_iff₀ (mul_pos hdelta hK)).2
    nlinarith
  exact ⟨b, hVpos, hVbound, hproduct⟩

end PrimesRestrictedDigits
