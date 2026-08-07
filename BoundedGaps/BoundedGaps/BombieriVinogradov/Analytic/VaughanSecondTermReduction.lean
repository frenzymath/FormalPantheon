import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReindex
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Vaughan's second-term finite reduction

This file formalizes `AkbaryHambrook2013v2`, Section 6, pp. 19--20,
equation (6.8), at natural endpoints. It stops before Pólya--Vinogradov.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- A complex Dirichlet-character sum over an inclusive natural interval. -/
noncomputable def dirichletCharacterIntervalSum
    (a b q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h ∈ Finset.Icc a b, χ h

/-- Maximum norm of suffix sums with natural lower endpoint through `x`,
totalized to zero when `x = 0`. -/
noncomputable def dirichletCharacterSuffixMaximum
    (x b q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun a ↦ ‖dirichletCharacterIntervalSum a b q χ‖)
  else 0

private theorem sum_log_sub_log_natPred_Icc (H : ℕ) :
    (∑ a ∈ Finset.Icc 2 H,
      (Real.log a - Real.log ((a - 1 : ℕ) : ℝ))) = Real.log H := by
  induction H with
  | zero => simp
  | succ H ih =>
      by_cases hH : 2 ≤ H + 1
      · rw [Finset.sum_Icc_succ_top hH, ih]
        have hpred : H + 1 - 1 = H := by omega
        rw [hpred]
        ring
      · have hzero : H = 0 := by omega
        subst H
        simp

/-- Discrete suffix form of logarithmic partial summation. -/
theorem sum_character_mul_log_eq_sum_logIncrement_mul_suffixes
    (H q : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ h ∈ Finset.Icc 1 H, χ h * (Real.log h : ℂ)) =
      ∑ a ∈ Finset.Icc 2 H,
        ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          dirichletCharacterIntervalSum a H q χ := by
  have htail (a : ℕ) (ha : a ∈ Finset.Icc 2 H) :
      dirichletCharacterIntervalSum a H q χ =
        ∑ h ∈ Finset.Icc 1 H, if a ≤ h then χ h else 0 := by
    have hfinset :
        Finset.Icc a H =
          (Finset.Icc 1 H).filter (fun h : ℕ ↦ a ≤ h) := by
      have haBounds := Finset.mem_Icc.mp ha
      ext h
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega
    rw [dirichletCharacterIntervalSum, hfinset, Finset.sum_filter]
  symm
  calc
    (∑ a ∈ Finset.Icc 2 H,
        ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          dirichletCharacterIntervalSum a H q χ) =
        ∑ a ∈ Finset.Icc 2 H,
          ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            ∑ h ∈ Finset.Icc 1 H, if a ≤ h then χ h else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [htail a ha]
    _ = ∑ h ∈ Finset.Icc 1 H,
        ∑ a ∈ Finset.Icc 2 H,
          ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (if a ≤ h then χ h else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.Icc 1 H, χ h * (Real.log h : ℂ) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hfilter :
          (Finset.Icc 2 H).filter (fun a : ℕ ↦ a ≤ h) =
            Finset.Icc 2 h := by
        have hhBounds := Finset.mem_Icc.mp hh
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      have hsumCast :
          (∑ a ∈ Finset.Icc 2 h,
            ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ)) =
              (Real.log h : ℂ) :=
        by
          rw [← Complex.ofReal_sum]
          exact congrArg (fun r : ℝ ↦ (r : ℂ))
            (sum_log_sub_log_natPred_Icc h)
      calc
        (∑ a ∈ Finset.Icc 2 H,
            ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
              (if a ≤ h then χ h else 0)) =
            (∑ a ∈ Finset.Icc 2 H,
              if a ≤ h then
                ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ)
              else 0) * χ h := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          split_ifs <;> simp
        _ = (∑ a ∈ Finset.Icc 2 h,
              ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ)) * χ h := by
          rw [← Finset.sum_filter, hfilter]
        _ = χ h * (Real.log h : ℂ) := by
          rw [hsumCast]
          exact mul_comm _ _

/-- Every interval represented in the suffix family is bounded by its finite
maximum. -/
theorem norm_dirichletCharacterIntervalSum_le_suffixMaximum
    {a x b q : ℕ} (ha : a ∈ Finset.Icc 1 x)
    (χ : DirichletCharacter ℂ q) :
    ‖dirichletCharacterIntervalSum a b q χ‖ ≤
      dirichletCharacterSuffixMaximum x b q χ := by
  unfold dirichletCharacterSuffixMaximum
  split_ifs with hx
  · exact Finset.le_sup' (fun c ↦ ‖dirichletCharacterIntervalSum c b q χ‖) ha
  · exact False.elim
      (hx ((Finset.mem_Icc.mp ha).1.trans (Finset.mem_Icc.mp ha).2))

/-- A logarithmically weighted initial character sum is controlled by the
largest suffix sum at a containing endpoint. -/
theorem norm_sum_character_mul_log_le_log_mul_suffixMaximum
    {H x q : ℕ} (hH : H ≤ x) (hx : 1 ≤ x)
    (χ : DirichletCharacter ℂ q) :
    ‖∑ h ∈ Finset.Icc 1 H, χ h * (Real.log h : ℂ)‖ ≤
      Real.log x * dirichletCharacterSuffixMaximum x H q χ := by
  rw [sum_character_mul_log_eq_sum_logIncrement_mul_suffixes]
  have hmaxNonneg :
      0 ≤ dirichletCharacterSuffixMaximum x H q χ :=
    (norm_nonneg (dirichletCharacterIntervalSum 1 H q χ)).trans
      (norm_dirichletCharacterIntervalSum_le_suffixMaximum
        (Finset.mem_Icc.mpr ⟨le_rfl, hx⟩) χ)
  calc
    ‖∑ a ∈ Finset.Icc 2 H,
        ((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          dirichletCharacterIntervalSum a H q χ‖ ≤
        ∑ a ∈ Finset.Icc 2 H,
          ‖((Real.log a - Real.log ((a - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            dirichletCharacterIntervalSum a H q χ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Icc 2 H,
        (Real.log a - Real.log ((a - 1 : ℕ) : ℝ)) *
          dirichletCharacterSuffixMaximum x H q χ := by
      apply Finset.sum_le_sum
      intro a ha
      have haBounds := Finset.mem_Icc.mp ha
      have hpredPos : 0 < ((a - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < a - 1 by omega)
      have hpredLe : ((a - 1 : ℕ) : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast Nat.sub_le a 1
      have hdelta :
          0 ≤ Real.log a - Real.log ((a - 1 : ℕ) : ℝ) :=
        sub_nonneg.mpr (Real.log_le_log hpredPos hpredLe)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdelta]
      gcongr
      exact norm_dirichletCharacterIntervalSum_le_suffixMaximum
        (Finset.mem_Icc.mpr ⟨by omega, haBounds.2.trans hH⟩) χ
    _ = Real.log H * dirichletCharacterSuffixMaximum x H q χ := by
      rw [← Finset.sum_mul, sum_log_sub_log_natPred_Icc]
    _ ≤ Real.log x * dirichletCharacterSuffixMaximum x H q χ := by
      by_cases hHzero : H = 0
      · subst H
        simp only [Nat.cast_zero, Real.log_zero, zero_mul]
        exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hx)) hmaxNonneg
      · apply mul_le_mul_of_nonneg_right _ hmaxNonneg
        exact Real.log_le_log
          (by exact_mod_cast (Nat.pos_of_ne_zero hHzero))
          (by exact_mod_cast hH)

/-- Natural-endpoint version of Akbary--Hambrook equation (6.8). -/
theorem norm_vaughanTwistedSumTwo_le_log_mul_sum_suffixMaximum
    {V : ℝ} {y q : ℕ} (hy : 1 ≤ y)
    (χ : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumTwo V y q χ‖ ≤
      Real.log y *
        ∑ d ∈ vaughanSecondTermIndices V y,
          dirichletCharacterSuffixMaximum y (y / d) q χ := by
  rw [vaughanTwistedSumTwo_eq_divisorLogSums]
  calc
    ‖∑ d ∈ vaughanSecondTermIndices V y,
        ((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
          ∑ h ∈ Finset.Icc 1 (y / d),
            χ h * (Real.log h : ℂ)‖ ≤
        ∑ d ∈ vaughanSecondTermIndices V y,
          ‖((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
            ∑ h ∈ Finset.Icc 1 (y / d),
              χ h * (Real.log h : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ vaughanSecondTermIndices V y,
        Real.log y *
          dirichletCharacterSuffixMaximum y (y / d) q χ := by
      apply Finset.sum_le_sum
      intro d hd
      have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := d)
      have hmu : ‖((ArithmeticFunction.moebius d : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast hmuInt
      have hinner :=
        norm_sum_character_mul_log_le_log_mul_suffixMaximum
          (H := y / d) (x := y) (Nat.div_le_self y d) hy χ
      calc
        ‖((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
            ∑ h ∈ Finset.Icc 1 (y / d),
              χ h * (Real.log h : ℂ)‖ =
            ‖((ArithmeticFunction.moebius d : ℝ) : ℂ)‖ * ‖χ d‖ *
              ‖∑ h ∈ Finset.Icc 1 (y / d),
                χ h * (Real.log h : ℂ)‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 *
              ‖∑ h ∈ Finset.Icc 1 (y / d),
                χ h * (Real.log h : ℂ)‖ := by
            gcongr
            exact χ.norm_le_one d
        _ ≤ Real.log y *
              dirichletCharacterSuffixMaximum y (y / d) q χ := by
            simpa using hinner
    _ = Real.log y *
        ∑ d ∈ vaughanSecondTermIndices V y,
          dirichletCharacterSuffixMaximum y (y / d) q χ := by
      rw [Finset.mul_sum]

/-- Any uniform bound for the suffix character sums controls the second
Vaughan term with the exact finite index cardinality. -/
theorem norm_vaughanTwistedSumTwo_le_card_mul_of_intervalBound
    {V C : ℝ} {y q : ℕ} (hy : 1 ≤ y)
    (χ : DirichletCharacter ℂ q)
    (hinterval :
      ∀ d ∈ vaughanSecondTermIndices V y,
        ∀ a ∈ Finset.Icc 1 y,
          ‖dirichletCharacterIntervalSum a (y / d) q χ‖ ≤ C) :
    ‖vaughanTwistedSumTwo V y q χ‖ ≤
      Real.log y * ((vaughanSecondTermIndices V y).card : ℝ) * C := by
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
  have hmax (d : ℕ) (hd : d ∈ vaughanSecondTermIndices V y) :
      dirichletCharacterSuffixMaximum y (y / d) q χ ≤ C := by
    rw [dirichletCharacterSuffixMaximum, dif_pos hy]
    apply Finset.sup'_le
    intro a ha
    exact hinterval d hd a ha
  calc
    ‖vaughanTwistedSumTwo V y q χ‖ ≤
        Real.log y *
          ∑ d ∈ vaughanSecondTermIndices V y,
            dirichletCharacterSuffixMaximum y (y / d) q χ :=
      norm_vaughanTwistedSumTwo_le_log_mul_sum_suffixMaximum hy χ
    _ ≤ Real.log y *
        ∑ _d ∈ vaughanSecondTermIndices V y, C := by
      gcongr with d hd
      exact hmax d hd
    _ = Real.log y * ((vaughanSecondTermIndices V y).card : ℝ) * C := by
      simp [mul_assoc]

/-- Source-shaped generic consumer for a uniform interval character-sum
bound. Pólya--Vinogradov is not asserted in this theorem. -/
theorem norm_vaughanTwistedSumTwo_le_cutoff_mul_of_intervalBound
    {V C : ℝ} {y q : ℕ} (hV : 1 ≤ V) (hy : 1 ≤ y)
    (hC : 0 ≤ C) (χ : DirichletCharacter ℂ q)
    (hinterval :
      ∀ d ∈ vaughanSecondTermIndices V y,
        ∀ a ∈ Finset.Icc 1 y,
          ‖dirichletCharacterIntervalSum a (y / d) q χ‖ ≤ C) :
    ‖vaughanTwistedSumTwo V y q χ‖ ≤ V * Real.log y * C := by
  have hcard := norm_vaughanTwistedSumTwo_le_card_mul_of_intervalBound
    hy χ hinterval
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
  have hcardCut := card_vaughanSecondTermIndices_le_cutoff hV y
  calc
    ‖vaughanTwistedSumTwo V y q χ‖ ≤
        Real.log y * ((vaughanSecondTermIndices V y).card : ℝ) * C := hcard
    _ ≤ Real.log y * V * C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardCut hlog) hC
    _ = V * Real.log y * C := by ring

end

end BoundedGaps.Maynard
