import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermTrivial
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermReindex

/-!
# Vaughan's small third-term bounds

This file proves the pointwise small-range estimate leading to
Akbary--Hambrook2013v2, Section 6, equation (6.12). The endpoint maximum and
weighted primitive-character aggregate remain in a separate owner.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Equation (6.11) bounds the small third term by character-prefix norms. -/
theorem norm_vaughanTwistedSumThreeSmall_le_log_mul_sum_prefix
    {U V : ℝ} {y q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumThreeSmall U V y q χ‖ ≤
      Real.log U *
        ∑ t ∈ vaughanThirdSmallIndices U y,
          ‖dirichletCharacterIntervalSum 1 (y / t) q χ‖ := by
  unfold vaughanTwistedSumThreeSmall
  calc
    ‖∑ t ∈ vaughanThirdSmallIndices U y,
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
          dirichletCharacterIntervalSum 1 (y / t) q χ‖ ≤
        ∑ t ∈ vaughanThirdSmallIndices U y,
          ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
            dirichletCharacterIntervalSum 1 (y / t) q χ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ vaughanThirdSmallIndices U y,
        Real.log U *
          ‖dirichletCharacterIntervalSum 1 (y / t) q χ‖ := by
      apply Finset.sum_le_sum
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hty, htU⟩
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_vaughanThirdCoefficient_mul_character_le_log_cutoff χ
          (Finset.mem_Icc.mp hty).1 htU)
        (norm_nonneg _)
    _ = Real.log U *
        ∑ t ∈ vaughanThirdSmallIndices U y,
          ‖dirichletCharacterIntervalSum 1 (y / t) q χ‖ := by
      rw [Finset.mul_sum]

private theorem norm_dirichletCharacterPrefixSum_le_upper
    {b q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖dirichletCharacterIntervalSum 1 b q χ‖ ≤ (b : ℝ) := by
  rw [dirichletCharacterIntervalSum]
  calc
    ‖∑ n ∈ Finset.Icc 1 b, χ n‖ ≤
        ∑ n ∈ Finset.Icc 1 b, ‖χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 b, (1 : ℝ) := by
      gcongr with n _hn
      exact χ.norm_le_one n
    _ = ((Finset.Icc 1 b).card : ℝ) := by simp
    _ = (b : ℝ) := by simp [Nat.card_Icc]

/-- Corrected non-strict level-one bound for the small third term. -/
theorem norm_vaughanTwistedSumThreeSmall_level_one_le_endpoint_mul_log_mul_one_add_log
    {U V : ℝ} {y : ℕ} (hU : 1 ≤ U)
    (χ : DirichletCharacter ℂ 1) :
    ‖vaughanTwistedSumThreeSmall U V y 1 χ‖ ≤
      (y : ℝ) * Real.log U * (1 + Real.log U) := by
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  calc
    ‖vaughanTwistedSumThreeSmall U V y 1 χ‖ ≤
        Real.log U *
          ∑ t ∈ vaughanThirdSmallIndices U y,
            ‖dirichletCharacterIntervalSum 1 (y / t) 1 χ‖ :=
      norm_vaughanTwistedSumThreeSmall_le_log_mul_sum_prefix χ
    _ ≤ Real.log U *
        ∑ t ∈ vaughanThirdSmallIndices U y,
          (y : ℝ) * ((t : ℝ))⁻¹ := by
      gcongr with t _ht
      calc
        ‖dirichletCharacterIntervalSum 1 (y / t) 1 χ‖ ≤
            ((y / t : ℕ) : ℝ) :=
          norm_dirichletCharacterPrefixSum_le_upper χ
        _ ≤ (y : ℝ) / (t : ℝ) := Nat.cast_div_le
        _ = (y : ℝ) * ((t : ℝ))⁻¹ := by rw [div_eq_mul_inv]
    _ = (y : ℝ) * Real.log U *
        ∑ t ∈ vaughanThirdSmallIndices U y, ((t : ℝ))⁻¹ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (y : ℝ) * Real.log U * (1 + Real.log U) := by
      gcongr
      simpa [vaughanThirdSmallIndices, vaughanSecondTermIndices] using
        sum_inv_vaughanSecondTermIndices_le_one_add_log hU y

/-- Strict final level-one estimate used in equation (6.12). -/
theorem norm_vaughanTwistedSumThreeSmall_level_one_lt_endpoint_mul_log_sq
    {U V : ℝ} {x y : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hyx : y ≤ x)
    (χ : DirichletCharacter ℂ 1) :
    ‖vaughanTwistedSumThreeSmall U V y 1 χ‖ <
      (x : ℝ) * (Real.log ((x : ℝ) * U)) ^ 2 := by
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hxone : (1 : ℝ) < x := by
    exact_mod_cast (show 1 < x by omega)
  have hUpos : (0 : ℝ) < U := zero_lt_one.trans_le hU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 := by
    convert Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hlogFour : (4 / 3 : ℝ) < Real.log 4 := by
    calc
      (4 / 3 : ℝ) = 2 * (2 / 3) := by ring
      _ < 2 * Real.log 2 := by nlinarith
      _ = Real.log 4 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
  have hlogFourLe : Real.log (4 : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogx : 1 < Real.log (x : ℝ) := by linarith
  have hlogStrict :
      Real.log U * (1 + Real.log U) <
        (Real.log ((x : ℝ) * U)) ^ 2 := by
    rw [Real.log_mul hxpos.ne' hUpos.ne']
    have hterm :
        0 ≤ Real.log U * (2 * Real.log (x : ℝ) - 1) :=
      mul_nonneg hlogU (by linarith)
    have hsquare : 0 < (Real.log (x : ℝ)) ^ 2 :=
      sq_pos_of_pos (zero_lt_one.trans hlogx)
    nlinarith
  have hfactor :
      0 ≤ Real.log U * (1 + Real.log U) := by positivity
  calc
    ‖vaughanTwistedSumThreeSmall U V y 1 χ‖ ≤
        (y : ℝ) * Real.log U * (1 + Real.log U) :=
      norm_vaughanTwistedSumThreeSmall_level_one_le_endpoint_mul_log_mul_one_add_log
        hU χ
    _ ≤ (x : ℝ) * (Real.log U * (1 + Real.log U)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hyx) hfactor
    _ < (x : ℝ) * (Real.log ((x : ℝ) * U)) ^ 2 :=
      mul_lt_mul_of_pos_left hlogStrict hxpos

/-- Primitive Polya--Vinogradov estimate for the small third term. -/
theorem norm_vaughanTwistedSumThreeSmall_lt_sqrt_mul_cutoff_mul_log_sq
    {Q U V : ℝ} {x y q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U)
    (hq : 1 < q) (hqQ : (q : ℝ) ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖vaughanTwistedSumThreeSmall U V y q χ‖ <
      Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrtq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hxone : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hsqrtxlt : Real.sqrt (x : ℝ) < (x : ℝ) :=
    Real.sqrt_lt_self_iff.mpr hxone
  have hxUpos : 0 < (x : ℝ) * U := by positivity
  have hU_lt_xU : U < (x : ℝ) * U := by nlinarith
  have hq_lt_xU : (q : ℝ) < (x : ℝ) * U :=
    (hqQ.trans hQsqrt).trans_lt (hsqrtxlt.trans_le (by nlinarith))
  have hlogU_lt : Real.log U < Real.log ((x : ℝ) * U) :=
    Real.strictMonoOn_log hUpos hxUpos hU_lt_xU
  have hlogq_lt : Real.log (q : ℝ) < Real.log ((x : ℝ) * U) :=
    Real.strictMonoOn_log hqpos hxUpos hq_lt_xU
  have hlogxUpos : 0 < Real.log ((x : ℝ) * U) :=
    Real.log_pos (hxone.trans_le (by nlinarith))
  have hlogs :
      Real.log U * Real.log (q : ℝ) <
        (Real.log ((x : ℝ) * U)) ^ 2 := by
    calc
      Real.log U * Real.log (q : ℝ) <
          Real.log ((x : ℝ) * U) * Real.log (q : ℝ) :=
        mul_lt_mul_of_pos_right hlogU_lt hlogq
      _ < Real.log ((x : ℝ) * U) * Real.log ((x : ℝ) * U) :=
        mul_lt_mul_of_pos_left hlogq_lt hlogxUpos
      _ = (Real.log ((x : ℝ) * U)) ^ 2 := by ring
  have hprefix (t : ℕ) (_ht : t ∈ vaughanThirdSmallIndices U y) :
      ‖dirichletCharacterIntervalSum 1 (y / t) q χ‖ ≤
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
      hq χ hχ 1 (y / t)).le
  calc
    ‖vaughanTwistedSumThreeSmall U V y q χ‖ ≤
        Real.log U *
          ∑ t ∈ vaughanThirdSmallIndices U y,
            ‖dirichletCharacterIntervalSum 1 (y / t) q χ‖ :=
      norm_vaughanTwistedSumThreeSmall_le_log_mul_sum_prefix χ
    _ ≤ Real.log U *
        ∑ _t ∈ vaughanThirdSmallIndices U y,
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr with t ht
      exact hprefix t ht
    _ = Real.log U * ((vaughanThirdSmallIndices U y).card : ℝ) *
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
      simp [mul_assoc]
    _ ≤ Real.log U * U *
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
      gcongr
      exact card_vaughanThirdSmallIndices_le_cutoff hU y
    _ = Real.sqrt (q : ℝ) * U *
        (Real.log U * Real.log (q : ℝ)) := by ring
    _ < Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
      gcongr

end

end BoundedGaps.Maynard
