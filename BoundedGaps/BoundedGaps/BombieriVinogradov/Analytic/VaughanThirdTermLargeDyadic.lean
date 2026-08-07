import BoundedGaps.BombieriVinogradov.Analytic.BilinearProductCutoffMaximum
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermReindex

/-!
# Dyadic decomposition of Vaughan's large third term

This file implements the exact dyadic decomposition preceding
Akbary--Hambrook's equation (6.13). The source's false strict count `T' < M`
is not used: each half-open block has ambient span `M` and may contain exactly
`M` integers.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 21--22. Semantic review:
`SEM-456`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Dyadic exponents that can contribute to an endpoint through `x`. The
condition `M < x` discards blocks whose `t` support through `x` is empty and
ensures that the later second ambient span `x / M` is positive. -/
def vaughanThirdLargeDyadicExponents
  (U V : ℝ) (x : ℕ) : Finset ℕ :=
  (dyadicExponentRange ⌊U * V⌋₊).filter (fun alpha ↦
    let M : ℕ := 2 ^ alpha
    U / 2 < (M : ℝ) ∧ (M : ℝ) ≤ U * V ∧ M < x)

/-- The original large-third-term support restricted to one dyadic block. -/
def vaughanThirdLargeDyadicIndices
    (U V : ℝ) (x alpha : ℕ) : Finset ℕ :=
  vaughanThirdLargeIndices U V x ∩ dyadicBlock alpha

/-- Fixed positive `r` support for the block at `2 ^ alpha`. -/
def vaughanThirdLargeDyadicRIndices
    (x alpha : ℕ) : Finset ℕ :=
  Finset.Icc 1 (x / 2 ^ alpha)

/-- One fixed-support bilinear block in the large third Vaughan term. -/
def vaughanTwistedSumThreeLargeDyadicBlock
    (U V : ℝ) (x y q alpha : ℕ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  bilinearProductCutoffSum y q chi
    (vaughanThirdLargeDyadicIndices U V x alpha)
    (vaughanThirdLargeDyadicRIndices x alpha)
    (fun t ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
    (fun _ ↦ 1)

/-- The active scale count is at most the source's logarithmic scale factor. -/
theorem card_vaughanThirdLargeDyadicExponents_le_log
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x : ℕ) :
    ((vaughanThirdLargeDyadicExponents U V x).card : ℝ) ≤
      Real.log (2 * U * V) / Real.log 2 := by
  have hUnonneg : 0 ≤ U := zero_le_one.trans hU
  have hUV : 1 ≤ U * V := by
    calc
      1 ≤ U := hU
      _ = U * 1 := (mul_one U).symm
      _ ≤ U * V := mul_le_mul_of_nonneg_left hV hUnonneg
  have hfloorPos : 0 < ⌊U * V⌋₊ := Nat.floor_pos.mpr hUV
  have hfloorLe : (⌊U * V⌋₊ : ℝ) ≤ U * V :=
    Nat.floor_le (zero_le_one.trans hUV)
  calc
    ((vaughanThirdLargeDyadicExponents U V x).card : ℝ) ≤
        ((dyadicExponentRange ⌊U * V⌋₊).card : ℝ) := by
      rw [vaughanThirdLargeDyadicExponents]
      exact_mod_cast Finset.card_filter_le
        (dyadicExponentRange ⌊U * V⌋₊) _
    _ ≤ Real.log (2 * (⌊U * V⌋₊ : ℝ)) / Real.log 2 :=
      card_dyadicExponentRange_le_log hfloorPos
    _ ≤ Real.log (2 * U * V) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
      apply Real.log_le_log (by positivity)
      calc
        2 * (⌊U * V⌋₊ : ℝ) ≤ 2 * (U * V) :=
          mul_le_mul_of_nonneg_left hfloorLe (by norm_num)
        _ = 2 * U * V := by ring

/-- Exact dyadic decomposition of the large third Vaughan term at every
natural endpoint `y ≤ x`. -/
theorem vaughanTwistedSumThreeLarge_eq_sum_dyadicBlocks
    {U V : ℝ} (hU : 1 ≤ U) (_hV : 1 ≤ V)
    {x y q : ℕ} (hy : y ≤ x)
    (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumThreeLarge U V y q chi =
      ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi := by
  let f : ℕ → ℂ := fun t ↦
    ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * chi t *
      dirichletCharacterIntervalSum 1 (y / t) q chi
  have hsupport : ∀ t ∈ vaughanThirdLargeIndices U V y,
      2 ≤ t ∧ t ≤ ⌊U * V⌋₊ := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨htIcc, htU, htUV⟩
    have htOneReal : (1 : ℝ) < t := hU.trans_lt htU
    have htOne : 1 < t := by exact_mod_cast htOneReal
    exact ⟨by omega, Nat.le_floor htUV⟩
  have hactive_of_mem {alpha t : ℕ}
      (ht : t ∈ vaughanThirdLargeIndices U V y)
      (htBlock : t ∈ dyadicBlock alpha) :
      alpha ∈ vaughanThirdLargeDyadicExponents U V x := by
    rcases Finset.mem_filter.mp ht with ⟨htIcc, htU, htUV⟩
    have htTwo := (hsupport t ht).1
    have htFloor := (hsupport t ht).2
    have hlog := (mem_dyadicBlock_iff_log_pred_eq htTwo).mp htBlock
    have hpredLe : t - 1 ≤ ⌊U * V⌋₊ := by omega
    have hlogLe : Nat.log 2 (t - 1) ≤ Nat.log 2 ⌊U * V⌋₊ :=
      Nat.log_mono_right hpredLe
    have halphaRange : alpha ∈ dyadicExponentRange ⌊U * V⌋₊ := by
      rw [dyadicExponentRange, Finset.mem_range]
      rw [hlog] at hlogLe
      exact Nat.lt_succ_of_le hlogLe
    have htBlockBounds := Finset.mem_Ioc.mp htBlock
    have htUpper : t ≤ 2 * 2 ^ alpha := by
      simpa only [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using
        htBlockBounds.2
    have hMltTReal : ((2 ^ alpha : ℕ) : ℝ) < t := by
      exact_mod_cast htBlockBounds.1
    have htUpperReal : (t : ℝ) ≤ 2 * (2 ^ alpha : ℕ) := by
      exact_mod_cast htUpper
    rw [vaughanThirdLargeDyadicExponents, Finset.mem_filter]
    refine ⟨halphaRange, ?_⟩
    dsimp only
    refine ⟨by linarith, hMltTReal.le.trans htUV, ?_⟩
    exact htBlockBounds.1.trans_le ((Finset.mem_Icc.mp htIcc).2.trans hy)
  have hactiveSubset :
      vaughanThirdLargeDyadicExponents U V x ⊆
        dyadicExponentRange ⌊U * V⌋₊ := by
    intro alpha halpha
    exact (Finset.mem_filter.mp
      (by simpa only [vaughanThirdLargeDyadicExponents] using halpha)).1
  have hblock_eq (alpha : ℕ) :
      (∑ t ∈ (vaughanThirdLargeIndices U V y).filter
          (fun t ↦ t ∈ dyadicBlock alpha), f t) =
        vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi := by
    let M := 2 ^ alpha
    let sm := vaughanThirdLargeDyadicIndices U V x alpha
    let sy := (vaughanThirdLargeIndices U V y).filter
      (fun t ↦ t ∈ dyadicBlock alpha)
    let sn := vaughanThirdLargeDyadicRIndices x alpha
    have hsySubset : sy ⊆ sm := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htLarge, htBlock⟩
      rcases Finset.mem_filter.mp htLarge with ⟨htIcc, htCutoffs⟩
      change t ∈ vaughanThirdLargeIndices U V x ∩ dyadicBlock alpha
      rw [Finset.mem_inter]
      refine ⟨Finset.mem_filter.mpr ⟨?_, htCutoffs⟩, htBlock⟩
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp htIcc).1, (Finset.mem_Icc.mp htIcc).2.trans hy⟩
    have hinner (t : ℕ) (ht : t ∈ sm) :
        sn.filter (fun r ↦ t * r ≤ y) = Finset.Icc 1 (y / t) := by
      rcases Finset.mem_inter.mp
        (by simpa only [sm, vaughanThirdLargeDyadicIndices] using ht) with
        ⟨htLarge, htBlock⟩
      have htPos : 0 < t := (Finset.mem_Icc.mp
        (Finset.mem_filter.mp htLarge).1).1
      have hMPos : 0 < M := by
        dsimp only [M]
        positivity
      have hMltT : M < t := (Finset.mem_Ioc.mp
        (by simpa only [M, dyadicBlock] using htBlock)).1
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc, sn,
        vaughanThirdLargeDyadicRIndices]
      constructor
      · rintro ⟨⟨hrPos, _hrX⟩, htr⟩
        refine ⟨hrPos, ?_⟩
        exact (Nat.le_div_iff_mul_le htPos).mpr
          (by simpa only [Nat.mul_comm] using htr)
      · rintro ⟨hrPos, hry⟩
        have htr : t * r ≤ y := by
          simpa only [Nat.mul_comm] using
            (Nat.le_div_iff_mul_le htPos).mp hry
        have hMr : M * r ≤ x := by
          calc
            M * r ≤ t * r := Nat.mul_le_mul_right r hMltT.le
            _ ≤ y := htr
            _ ≤ x := hy
        refine ⟨⟨hrPos, ?_⟩, htr⟩
        exact (Nat.le_div_iff_mul_le hMPos).mpr
          (by simpa only [M, Nat.mul_comm] using hMr)
    have hsumInner (t : ℕ) (ht : t ∈ sm) :
        (∑ r ∈ sn.filter (fun r ↦ t * r ≤ y),
          ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * 1 * chi (t * r)) =
          f t := by
      rw [hinner t ht]
      simp only [f, dirichletCharacterIntervalSum, mul_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [map_mul]
      ring
    have hsumSubset :
        (∑ t ∈ sm, f t) = ∑ t ∈ sy, f t := by
      symm
      apply Finset.sum_subset hsySubset
      intro t htSm htNotSy
      rcases Finset.mem_inter.mp
        (by simpa only [sm, vaughanThirdLargeDyadicIndices] using htSm) with
        ⟨htLarge, htBlock⟩
      have htNotLarge : t ∉ vaughanThirdLargeIndices U V y := by
        intro htLargeY
        exact htNotSy (Finset.mem_filter.mpr ⟨htLargeY, htBlock⟩)
      have hyt : y < t := by
        by_contra hnot
        apply htNotLarge
        rcases Finset.mem_filter.mp htLarge with ⟨htIcc, htCutoffs⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp htIcc).1, Nat.le_of_not_gt hnot⟩, htCutoffs⟩
      simp only [f, dirichletCharacterIntervalSum, Nat.div_eq_of_lt hyt]
      simp
    symm
    calc
      vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi =
          ∑ t ∈ sm, ∑ r ∈ sn.filter (fun r ↦ t * r ≤ y),
            ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * 1 * chi (t * r) := by
        rfl
      _ = ∑ t ∈ sm, f t := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hsumInner t ht
      _ = ∑ t ∈ sy, f t := hsumSubset
      _ = ∑ t ∈ (vaughanThirdLargeIndices U V y).filter
          (fun t ↦ t ∈ dyadicBlock alpha), f t := rfl
  change (∑ t ∈ vaughanThirdLargeIndices U V y, f t) = _
  calc
    (∑ t ∈ vaughanThirdLargeIndices U V y, f t) =
        ∑ alpha ∈ dyadicExponentRange ⌊U * V⌋₊,
          ∑ t ∈ (vaughanThirdLargeIndices U V y).filter
            (fun t ↦ t ∈ dyadicBlock alpha), f t :=
      sum_eq_sum_dyadicBlocks (vaughanThirdLargeIndices U V y) hsupport f
    _ = ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        ∑ t ∈ (vaughanThirdLargeIndices U V y).filter
          (fun t ↦ t ∈ dyadicBlock alpha), f t := by
      symm
      apply Finset.sum_subset hactiveSubset
      intro alpha halphaRange halphaNotActive
      apply Finset.sum_eq_zero
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htLarge, htBlock⟩
      exact False.elim (halphaNotActive (hactive_of_mem htLarge htBlock))
    _ = ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      exact hblock_eq alpha

end

end BoundedGaps.Maynard
