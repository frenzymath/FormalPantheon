import BoundedGaps.BombieriVinogradov.Analytic.BilinearProductCutoffMaximum
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermReindex

/-!
# Dyadic decomposition of Vaughan's fourth term

This file implements the exact dyadic decomposition before
Akbary--Hambrook2013v2, equation (6.15). The fixed rectangular `k` support is
filtered by the original product endpoint, and the fourth-term minus sign is
kept outside every complete block.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 22--23. Semantic review:
`SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Dyadic scales that can contribute to the fourth Vaughan term through
`x`. The strict upper condition removes the empty boundary scale. -/
def vaughanFourthDyadicExponents
    (U V : ℝ) (x : ℕ) : Finset ℕ :=
  (dyadicExponentRange ⌊(x : ℝ) / V⌋₊).filter (fun alpha ↦
    let M : ℕ := 2 ^ alpha
    U / 2 < (M : ℝ) ∧ (M : ℝ) < (x : ℝ) / V)

/-- Fixed `m` support at the fourth-term dyadic scale `2^alpha`. -/
def vaughanFourthDyadicMIndices
    (U V : ℝ) (x alpha : ℕ) : Finset ℕ :=
  (dyadicBlock alpha).filter (fun m ↦
    U < (m : ℝ) ∧ (m : ℝ) ≤ (x : ℝ) / V)

/-- Fixed positive `k` support at the fourth-term dyadic scale `2^alpha`. -/
def vaughanFourthDyadicKIndices
    (V : ℝ) (x alpha : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (x / 2 ^ alpha)).filter (fun k ↦ V < (k : ℝ))

/-- One fixed-support bilinear block in the fourth Vaughan term. -/
def vaughanTwistedSumFourDyadicBlock
    (U V : ℝ) (x y q alpha : ℕ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  -bilinearProductCutoffSum y q chi
    (vaughanFourthDyadicMIndices U V x alpha)
    (vaughanFourthDyadicKIndices V x alpha)
    (fun m ↦ ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
    (fun k ↦ ((vaughanFourthCoefficient V k : ℝ) : ℂ))

/-- Exact dyadic decomposition of the fourth Vaughan term at every natural
endpoint `y ≤ x`. -/
theorem vaughanTwistedSumFour_eq_sum_dyadicBlocks
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {x y q : ℕ} (hy : y ≤ x)
    (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumFour U V y q chi =
      ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        vaughanTwistedSumFourDyadicBlock U V x y q alpha chi := by
  let source : Finset ℕ :=
    (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ))
  let s : Finset ℕ :=
    (Finset.Icc 1 y).filter (fun m : ℕ ↦
      U < (m : ℝ) ∧ (m : ℝ) ≤ (x : ℝ) / V)
  let f : ℕ → ℕ → ℂ := fun m k ↦
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
      ((vaughanFourthCoefficient V k : ℝ) : ℂ) * chi (m * k)
  let g : ℕ → ℂ := fun m ↦
    ∑ k ∈ (Finset.Icc 1 (y / m)).filter
      (fun k : ℕ ↦ V < (k : ℝ)), f m k
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hs_eq :
      s = source.filter (fun m : ℕ ↦ (m : ℝ) ≤ (x : ℝ) / V) := by
    ext m
    simp only [s, source, Finset.mem_filter]
    tauto
  have hsource : (∑ m ∈ source, g m) = ∑ m ∈ s, g m := by
    rw [hs_eq]
    symm
    apply Finset.sum_filter_of_ne
    intro m hm hgm
    by_contra hmCap
    have hmPos : 0 < m := (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (by simpa only [source] using hm)).1).1
    have hzero : g m = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkV⟩
      have hmk : m * k ≤ y := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hmPos).mp (Finset.mem_Icc.mp hkIcc).2
      have hmkReal : ((m * k : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast hmk.trans hy
      have hmV : (m : ℝ) * V < ((m * k : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        exact mul_lt_mul_of_pos_left hkV (Nat.cast_pos.mpr hmPos)
      have hmLt : (m : ℝ) < (x : ℝ) / V :=
        (lt_div_iff₀ hVpos).2 (hmV.trans_le hmkReal)
      exact False.elim (hmCap hmLt.le)
    exact hgm hzero
  have hsupport : ∀ m ∈ s,
      2 ≤ m ∧ m ≤ ⌊(x : ℝ) / V⌋₊ := by
    intro m hm
    rcases Finset.mem_filter.mp (by simpa only [s] using hm) with
      ⟨hmIcc, hmU, hmCap⟩
    have hmOneReal : (1 : ℝ) < m := hU.trans_lt hmU
    have hmOne : 1 < m := by exact_mod_cast hmOneReal
    exact ⟨by omega, Nat.le_floor hmCap⟩
  have hactive_of_mem {alpha m : ℕ}
      (hm : m ∈ s) (hmBlock : m ∈ dyadicBlock alpha) :
      alpha ∈ vaughanFourthDyadicExponents U V x := by
    rcases Finset.mem_filter.mp (by simpa only [s] using hm) with
      ⟨_hmIcc, hmU, hmCap⟩
    have hmTwo := (hsupport m hm).1
    have hmFloor := (hsupport m hm).2
    have hlog := (mem_dyadicBlock_iff_log_pred_eq hmTwo).mp hmBlock
    have hpredLe : m - 1 ≤ ⌊(x : ℝ) / V⌋₊ := by omega
    have hlogLe :
        Nat.log 2 (m - 1) ≤ Nat.log 2 ⌊(x : ℝ) / V⌋₊ :=
      Nat.log_mono_right hpredLe
    have halphaRange :
        alpha ∈ dyadicExponentRange ⌊(x : ℝ) / V⌋₊ := by
      rw [dyadicExponentRange, Finset.mem_range]
      rw [hlog] at hlogLe
      exact Nat.lt_succ_of_le hlogLe
    have hmBlockBounds := Finset.mem_Ioc.mp hmBlock
    have hmUpper : m ≤ 2 * 2 ^ alpha := by
      simpa only [dyadicBlock, pow_succ, Nat.succ_eq_add_one,
        Nat.mul_comm] using hmBlockBounds.2
    have hMltMReal : ((2 ^ alpha : ℕ) : ℝ) < m := by
      exact_mod_cast hmBlockBounds.1
    have hmUpperReal : (m : ℝ) ≤ 2 * (2 ^ alpha : ℕ) := by
      exact_mod_cast hmUpper
    rw [vaughanFourthDyadicExponents, Finset.mem_filter]
    refine ⟨halphaRange, ?_⟩
    dsimp only
    exact ⟨by linarith, hMltMReal.trans_le hmCap⟩
  have hactiveSubset :
      vaughanFourthDyadicExponents U V x ⊆
        dyadicExponentRange ⌊(x : ℝ) / V⌋₊ := by
    intro alpha halpha
    exact (Finset.mem_filter.mp
      (by simpa only [vaughanFourthDyadicExponents] using halpha)).1
  have hblock_eq (alpha : ℕ) :
      -(∑ m ∈ s.filter (fun m ↦ m ∈ dyadicBlock alpha), g m) =
        vaughanTwistedSumFourDyadicBlock U V x y q alpha chi := by
    let M : ℕ := 2 ^ alpha
    let sm := vaughanFourthDyadicMIndices U V x alpha
    let sy := s.filter (fun m ↦ m ∈ dyadicBlock alpha)
    let sn := vaughanFourthDyadicKIndices V x alpha
    have hsySubset : sy ⊆ sm := by
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmS, hmBlock⟩
      rcases Finset.mem_filter.mp (by simpa only [s] using hmS) with
        ⟨_hmIcc, hmCuts⟩
      exact Finset.mem_filter.mpr ⟨hmBlock, hmCuts⟩
    have hinner (m : ℕ) (hm : m ∈ sm) :
        sn.filter (fun k ↦ m * k ≤ y) =
          (Finset.Icc 1 (y / m)).filter (fun k : ℕ ↦ V < (k : ℝ)) := by
      rcases Finset.mem_filter.mp
        (by simpa only [sm, vaughanFourthDyadicMIndices] using hm) with
        ⟨hmBlock, _hmCuts⟩
      have hMltM : M < m := (Finset.mem_Ioc.mp
        (by simpa only [M, dyadicBlock] using hmBlock)).1
      have hmPos : 0 < m := by
        have hMPos : 0 < M := by
          dsimp only [M]
          positivity
        exact hMPos.trans hMltM
      have hMPos : 0 < M := by
        dsimp only [M]
        positivity
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
        sn, vaughanFourthDyadicKIndices]
      constructor
      · rintro ⟨⟨⟨hkPos, _hkX⟩, hkV⟩, hmk⟩
        refine ⟨⟨hkPos, ?_⟩, hkV⟩
        exact (Nat.le_div_iff_mul_le hmPos).mpr
          (by simpa only [Nat.mul_comm] using hmk)
      · rintro ⟨⟨hkPos, hky⟩, hkV⟩
        have hmk : m * k ≤ y := by
          simpa only [Nat.mul_comm] using
            (Nat.le_div_iff_mul_le hmPos).mp hky
        have hMk : M * k ≤ x := by
          calc
            M * k ≤ m * k := Nat.mul_le_mul_right k hMltM.le
            _ ≤ y := hmk
            _ ≤ x := hy
        refine ⟨⟨⟨hkPos, ?_⟩, hkV⟩, hmk⟩
        exact (Nat.le_div_iff_mul_le hMPos).mpr
          (by simpa only [M, Nat.mul_comm] using hMk)
    have hsumInner (m : ℕ) (hm : m ∈ sm) :
        (∑ k ∈ sn.filter (fun k ↦ m * k ≤ y), f m k) = g m := by
      rw [hinner m hm]
    have hsumSubset : (∑ m ∈ sm, g m) = ∑ m ∈ sy, g m := by
      symm
      apply Finset.sum_subset hsySubset
      intro m hmSm hmNotSy
      rcases Finset.mem_filter.mp
        (by simpa only [sm, vaughanFourthDyadicMIndices] using hmSm) with
        ⟨hmBlock, hmCuts⟩
      have hmNotS : m ∉ s := by
        intro hmS
        exact hmNotSy (Finset.mem_filter.mpr ⟨hmS, hmBlock⟩)
      have hym : y < m := by
        by_contra hnot
        apply hmNotS
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr
            ⟨by
              have hMPos : 0 < (2 ^ alpha : ℕ) := by positivity
              exact hMPos.trans (Finset.mem_Ioc.mp
                (by simpa only [dyadicBlock] using hmBlock)).1,
              Nat.le_of_not_gt hnot⟩,
            hmCuts⟩
      simp only [g, Nat.div_eq_of_lt hym]
      simp
    symm
    calc
      vaughanTwistedSumFourDyadicBlock U V x y q alpha chi =
          -(∑ m ∈ sm, ∑ k ∈ sn.filter (fun k ↦ m * k ≤ y), f m k) := by
        rfl
      _ = -(∑ m ∈ sm, g m) := by
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro m hm
        exact hsumInner m hm
      _ = -(∑ m ∈ sy, g m) := congrArg Neg.neg hsumSubset
      _ = -(∑ m ∈ s.filter (fun m ↦ m ∈ dyadicBlock alpha), g m) := rfl
  rw [vaughanTwistedSumFour_eq_nestedFactorSum]
  change -(∑ m ∈ source, g m) = _
  rw [hsource]
  calc
    -(∑ m ∈ s, g m) =
        ∑ alpha ∈ dyadicExponentRange ⌊(x : ℝ) / V⌋₊,
          -(∑ m ∈ s.filter (fun m ↦ m ∈ dyadicBlock alpha), g m) := by
      rw [sum_eq_sum_dyadicBlocks s hsupport g]
      rw [← Finset.sum_neg_distrib]
    _ = ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        -(∑ m ∈ s.filter (fun m ↦ m ∈ dyadicBlock alpha), g m) := by
      symm
      apply Finset.sum_subset hactiveSubset
      intro alpha halphaRange halphaNotActive
      apply neg_eq_zero.mpr
      apply Finset.sum_eq_zero
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmS, hmBlock⟩
      exact False.elim (halphaNotActive (hactive_of_mem hmS hmBlock))
    _ = ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        vaughanTwistedSumFourDyadicBlock U V x y q alpha chi := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      exact hblock_eq alpha

end

end BoundedGaps.Maynard
