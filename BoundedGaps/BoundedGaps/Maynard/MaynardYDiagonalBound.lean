import BoundedGaps.Maynard.MaynardYDiagonalExplicit
import BoundedGaps.Maynard.MaynardS1StarredSummandBound

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! A finite product envelope for the explicit Y-diagonal. -/

theorem maynardDivisorTupleSupport_subset_preSievedCommonTupleSupport
    (H : Finset ℕ) (R W : ℕ) :
    maynardDivisorTupleSupport H R W ⊆
      preSievedCommonTupleSupport H W R := by
  classical
  intro u hu
  rw [preSievedCommonTupleSupport, Fintype.mem_piFinset]
  intro h
  rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
  have huSupport := isMaynardDivisorTuple_of_mem_support hu
  have huBox := huSupport.mem_maynardDivisorTupleBox
  have huBounds := (mem_maynardDivisorTupleBox_iff.mp huBox h)
  have huSquarefree := huSupport.coordinate_squarefree h
  have huPositive : 0 < u h :=
    Nat.pos_of_ne_zero huSquarefree.ne_zero
  exact ⟨Finset.mem_range.mpr huBounds.2,
    ⟨huPositive, ⟨huSquarefree, huSupport.coordinate_coprime_W h⟩⟩⟩

theorem maynardYDiagonalSum_abs_le_commonTupleMean
    {H : Finset ℕ} {R W : ℕ} {F : (H → ℝ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B) :
    |maynardYDiagonalSum H R W (maynardYValue H R W F)| ≤
      B ^ 2 * (squarefreeCoprimeInvTotientMean W R) ^ Fintype.card H := by
  classical
  have hsubset : maynardDivisorTupleSupport H R W ⊆
      preSievedCommonTupleSupport H W R :=
    maynardDivisorTupleSupport_subset_preSievedCommonTupleSupport H R W
  rw [maynardYDiagonalSum_maynardYValue_eq_explicit]
  calc
    |∑ u ∈ maynardDivisorTupleSupport H R W,
        F (fun h => Real.log (u h) / Real.log R) ^ 2 /
          ∏ h : H, (Nat.totient (u h) : ℝ)| ≤
        ∑ u ∈ maynardDivisorTupleSupport H R W,
          B ^ 2 / (commonTotientProduct H u : ℝ) := by
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      apply Finset.sum_le_sum
      intro u hu
      have huSupport := isMaynardDivisorTuple_of_mem_support hu
      have huCommon : u ∈ preSievedCommonTupleSupport H W R := hsubset hu
      have hdenNat := commonTotientProduct_pos_of_preSieved huCommon
      have hden : 0 < (commonTotientProduct H u : ℝ) := by
        exact_mod_cast hdenNat
      have hFval := hF (fun h => Real.log (u h) / Real.log R)
      have hprod : (commonTotientProduct H u : ℝ) =
          ∏ h : H, (Nat.totient (u h) : ℝ) := by
        unfold commonTotientProduct
        push_cast
        simp
      rw [abs_div, abs_pow, ← hprod, abs_of_pos hden]
      have hsq : |F (fun h => Real.log (u h) / Real.log R)| ^ 2 ≤ B ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hB).mpr hFval
      exact div_le_div_of_nonneg_right hsq hden.le
    _ = B ^ 2 *
          ∑ u ∈ maynardDivisorTupleSupport H R W,
            (1 : ℝ) / (commonTotientProduct H u : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      field_simp
    _ ≤ B ^ 2 * commonTupleInvTotientMean H W R := by
      unfold commonTupleInvTotientMean
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          exact hsubset hu
        · intro u huSupport huNot
          have huNonneg : 0 ≤ (1 : ℝ) /
              (commonTotientProduct H u : ℝ) := by
            positivity
          exact huNonneg
      · positivity
    _ ≤ B ^ 2 * (squarefreeCoprimeInvTotientMean W R) ^ Fintype.card H := by
      apply mul_le_mul_of_nonneg_left
        (commonTupleInvTotientMean_le H W R)
      positivity

theorem abs_engelsmaMaynardYDiagonal_le_commonMean
    {alpha : ℝ} (N : ℕ) :
    |engelsmaMaynardYDiagonal alpha N| ≤
      smallKCandidateBound ^ 2 *
        (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N)) ^
          Fintype.card BoundedGaps.engelsmaTuple := by
  unfold engelsmaMaynardYDiagonal
  apply maynardYDiagonalSum_abs_le_commonTupleMean
    smallKCandidateBound_nonneg
  exact engelsmaSmallKCandidate_abs_le

end BoundedGaps.Maynard
