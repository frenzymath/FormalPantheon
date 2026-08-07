import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronSeries
import BoundedGaps.BombieriVinogradov.Analytic.PrincipalZetaPole
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Von Mangoldt bounds for the modified Perron bridge

This file specializes the generic Perron error terms to character-twisted von
Mangoldt coefficients. The near-diagonal contribution is finite and bounded
by two harmonic sums; the absolute coefficient mass is dominated by the
coefficient-one zeta series from SEM-468.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section

private lemma sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) =
      (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]

private lemma sum_inv_abs_sub_lower (x : ℕ) :
    (∑ n ∈ Finset.Ico 1 x,
      |(x : ℝ) - n|⁻¹) = (harmonic (x - 1) : ℝ) := by
  have hreflect := Finset.sum_Ico_reflect
    (fun k : ℕ => ((k : ℝ))⁻¹) 1
    (m := x) (n := x) (by omega)
  have hb1 : x + 1 - x = 1 := by omega
  have hb2 : x + 1 - 1 = x := by omega
  rw [hb1, hb2] at hreflect
  calc
    (∑ n ∈ Finset.Ico 1 x, |(x : ℝ) - n|⁻¹) =
        ∑ n ∈ Finset.Ico 1 x, (((x - n : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnx := (Finset.mem_Ico.mp hn).2.le
      have hnonneg : (0 : ℝ) ≤ (x : ℝ) - n :=
        sub_nonneg.mpr (by exact_mod_cast hnx)
      rw [abs_of_nonneg hnonneg, Nat.cast_sub hnx]
    _ = ∑ k ∈ Finset.Ico 1 x, ((k : ℝ))⁻¹ := hreflect
    _ = (harmonic (x - 1) : ℝ) := by
      by_cases hx : x = 0
      · simp [hx]
      have hxid : (x - 1) + 1 = x := by omega
      simpa [hxid] using sum_Ico_inv_eq_harmonic (x - 1)

private lemma sum_inv_abs_sub_upper (x : ℕ) :
    (∑ n ∈ Finset.Ico (x + 1) (2 * x),
      |(x : ℝ) - n|⁻¹) = (harmonic (x - 1) : ℝ) := by
  by_cases hx : x = 0
  · simp [hx]
  have hsum :
      (∑ n ∈ Finset.Ico (x + 1) (2 * x),
        (((n - x : ℕ) : ℝ))⁻¹) =
        ∑ k ∈ Finset.Ico 1 x, ((k : ℝ))⁻¹ := by
    refine Finset.sum_bij'
      (fun n _ => n - x) (fun k _ => x + k) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have h := Finset.mem_Ico.mp hn
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro k hk
      have h := Finset.mem_Ico.mp hk
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro n hn
      have h := Finset.mem_Ico.mp hn
      omega
    · intro k hk
      omega
    · intro n hn
      rfl
  calc
    (∑ n ∈ Finset.Ico (x + 1) (2 * x),
        |(x : ℝ) - n|⁻¹) =
        ∑ n ∈ Finset.Ico (x + 1) (2 * x),
          (((n - x : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hxn := (Finset.mem_Ico.mp hn).1
      have hxle : x ≤ n := by omega
      have hnonpos : (x : ℝ) - n ≤ 0 :=
        sub_nonpos.mpr (by exact_mod_cast hxle)
      rw [abs_of_nonpos hnonpos, neg_sub, Nat.cast_sub hxle]
    _ = ∑ k ∈ Finset.Ico 1 x, ((k : ℝ))⁻¹ := hsum
    _ = (harmonic (x - 1) : ℝ) := by
      have hxid : (x - 1) + 1 = x := by omega
      simpa [hxid] using sum_Ico_inv_eq_harmonic (x - 1)

private lemma tsum_inv_abs_sub_ne_le
    (x : ℕ) :
    (∑' n : ℕ,
      if 0 < n ∧ (n : ℝ) < 2 * x ∧ n ≠ x then
        |(x : ℝ) - n|⁻¹ else 0) ≤
      2 * (harmonic x : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Ico 1 (2 * x)) (by
    intro n hn
    have hnOut : n < 1 ∨ 2 * x ≤ n := by
      simp only [Finset.mem_Ico] at hn
      omega
    split_ifs with h
    · rcases hnOut with hnLow | hnHigh
      · omega
      · have hnHighReal : 2 * (x : ℝ) ≤ n := by
          exact_mod_cast hnHigh
        have hnot : ¬ (n : ℝ) < 2 * x := not_lt.mpr hnHighReal
        exact (hnot h.2.1).elim
    · rfl)]
  rw [← Finset.sum_filter]
  let S := (Finset.Ico 1 (2 * x)).filter fun n => n ≠ x
  have hfilter :
      (Finset.Ico 1 (2 * x)).filter
          (fun n : ℕ => 0 < n ∧ (n : ℝ) < 2 * x ∧ n ≠ x) = S := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · intro h
      exact ⟨h.1, h.2.2.2⟩
    · intro h
      have hnPos : 0 < n := by omega
      have hnUpper : (n : ℝ) < 2 * x := by exact_mod_cast h.1.2
      exact ⟨h.1, hnPos, hnUpper, h.2⟩
  have hsplit : S = Finset.Ico 1 x ∪ Finset.Ico (x + 1) (2 * x) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_union]
    omega
  rw [hfilter, hsplit, Finset.sum_union]
  · rw [sum_inv_abs_sub_lower, sum_inv_abs_sub_upper]
    have hmono : (harmonic (x - 1) : ℝ) ≤ (harmonic x : ℝ) := by
      by_cases hx : x = 0
      · simp [hx]
      have hxid : x = (x - 1) + 1 := by omega
      have hharmonic :
          harmonic x = harmonic (x - 1) + ((x : ℚ))⁻¹ := by
        calc
          harmonic x = harmonic ((x - 1) + 1) := congrArg harmonic hxid
          _ = harmonic (x - 1) + (((x - 1 + 1 : ℕ) : ℚ))⁻¹ :=
            harmonic_succ (x - 1)
          _ = harmonic (x - 1) + ((x : ℚ))⁻¹ := by rw [← hxid]
      rw [hharmonic, Rat.cast_add]
      exact le_add_of_nonneg_right (by positivity)
    linarith
  · simp only [Finset.disjoint_left, Finset.mem_Ico]
    omega

private lemma one_le_log_natCast_of_four_le
    {x : ℕ} (hx : 4 ≤ x) :
    (1 : ℝ) ≤ Real.log x := by
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  calc
    (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    _ = Real.log 4 := Real.log_four_eq.symm
    _ ≤ Real.log (x : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hx)

private lemma summable_dirichletPerronNearMass
    (a : ℕ → ℂ) (x : ℕ) (U : ℝ) :
    Summable fun n : ℕ => ‖a n‖ * dirichletPerronNearError x U n := by
  refine summable_of_ne_finset_zero (s := Finset.range (2 * x)) ?_
  intro n hn
  have hnLower : 2 * x ≤ n := by simpa using hn
  rw [dirichletPerronNearError, if_neg]
  · simp
  · intro h
    have hnLowerReal : 2 * (x : ℝ) ≤ n := by exact_mod_cast hnLower
    exact (not_lt_of_ge hnLowerReal) h.2.2.1

private lemma summable_inv_abs_sub_ne (x : ℕ) :
    Summable fun n : ℕ =>
      if 0 < n ∧ (n : ℝ) < 2 * x ∧ n ≠ x then
        |(x : ℝ) - n|⁻¹ else 0 := by
  refine summable_of_ne_finset_zero (s := Finset.Ico 1 (2 * x)) ?_
  intro n hn
  rw [if_neg]
  intro h
  apply hn
  exact Finset.mem_Ico.mpr ⟨h.1, by exact_mod_cast h.2.1⟩

/-- The character-twisted von Mangoldt near-diagonal mass has the explicit
project constant required by the generic Perron theorem. -/
theorem dirichletPerronNearMass_twist_vonMangoldt_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {x : ℕ} {U : ℝ} (hx : 4 ≤ x) (hU : 0 < U) :
    dirichletPerronNearMass
        ((fun n : ℕ => chi n) *
          fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x U ≤
      32 * (x : ℝ) * Real.log x ^ 2 / U := by
  let a : ℕ → ℂ :=
    (fun n : ℕ => chi n) *
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let r : ℕ → ℝ := fun n =>
    if 0 < n ∧ (n : ℝ) < 2 * x ∧ n ≠ x then
      |(x : ℝ) - n|⁻¹ else 0
  let K : ℝ := 4 * (x : ℝ) * Real.log x / U
  have hxPos : 0 < x := by omega
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hxPos
  have hlogOne := one_le_log_natCast_of_four_le hx
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint (n : ℕ) :
      ‖a n‖ * dirichletPerronNearError x U n ≤ K * r n := by
    rw [dirichletPerronNearError]
    split_ifs with hn
    · have hnPosReal : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hnUpper : (n : ℝ) ≤ 2 * x := hn.2.2.1.le
      have hlogn : Real.log n ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log hnPosReal hnUpper
      have hlogTwoLe : Real.log 2 ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ x by omega))
      have hlogTwoX : Real.log (2 * (x : ℝ)) ≤
          2 * Real.log x := by
        rw [Real.log_mul (by norm_num) hxReal.ne']
        linarith
      have hcoeff : ‖a n‖ ≤ 2 * Real.log x := by
        calc
          ‖a n‖ = ‖chi n‖ * ArithmeticFunction.vonMangoldt n := by
            simp only [a, Pi.mul_apply, norm_mul]
            rw [Complex.norm_of_nonneg
              ArithmeticFunction.vonMangoldt_nonneg]
          _ ≤ ArithmeticFunction.vonMangoldt n := by
            simpa using mul_le_mul_of_nonneg_right
              (chi.norm_le_one (n : ZMod q))
              ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log (2 * (x : ℝ)) := hlogn
          _ ≤ 2 * Real.log x := hlogTwoX
      have hcastNe : (x : ℝ) ≠ (n : ℝ) := by
        exact_mod_cast hn.2.2.2.symm
      have habs : 0 < |(x : ℝ) - n| :=
        abs_pos.mpr (sub_ne_zero.mpr hcastNe)
      have hnearNonneg :
          0 ≤ min 1 (2 * (x : ℝ) /
            (U * |(x : ℝ) - n|)) := by
        exact le_min (by norm_num)
          (div_nonneg (by positivity) (mul_nonneg hU.le habs.le))
      have hnear :
          min 1 (2 * (x : ℝ) /
              (U * |(x : ℝ) - n|)) ≤
            2 * (x : ℝ) / (U * |(x : ℝ) - n|) :=
        min_le_right _ _
      have hr : r n = |(x : ℝ) - n|⁻¹ := by
        dsimp [r]
        rw [if_pos ⟨hn.1, hn.2.2.1, hn.2.2.2⟩]
      rw [hr]
      calc
        ‖a n‖ * min 1 (2 * (x : ℝ) /
            (U * |(x : ℝ) - n|)) ≤
            (2 * Real.log x) * min 1 (2 * (x : ℝ) /
              (U * |(x : ℝ) - n|)) :=
          mul_le_mul_of_nonneg_right hcoeff hnearNonneg
        _ ≤ (2 * Real.log x) *
            (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) :=
          mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = K * |(x : ℝ) - n|⁻¹ := by
          dsimp [K]
          field_simp [hU.ne', habs.ne']
          ring
    · simp only [mul_zero]
      exact mul_nonneg hK (by
        dsimp [r]
        split_ifs
        · positivity
        · rfl)
  have hleft := summable_dirichletPerronNearMass a x U
  have hright : Summable fun n : ℕ => K * r n :=
    (summable_inv_abs_sub_ne x).mul_left K
  have hrBound : (∑' n : ℕ, r n) ≤ 2 * (harmonic x : ℝ) := by
    simpa [r] using tsum_inv_abs_sub_ne_le x
  have hHarmonic : (harmonic x : ℝ) ≤ 2 * Real.log x := by
    have hraw : (harmonic x : ℝ) ≤ 1 + Real.log x :=
      harmonic_le_one_add_log x
    linarith
  change (∑' n : ℕ, ‖a n‖ * dirichletPerronNearError x U n) ≤ _
  calc
    (∑' n : ℕ, ‖a n‖ * dirichletPerronNearError x U n) ≤
        ∑' n : ℕ, K * r n :=
      hleft.tsum_le_tsum hpoint hright
    _ = K * ∑' n : ℕ, r n := tsum_mul_left
    _ ≤ K * (2 * (harmonic x : ℝ)) :=
      mul_le_mul_of_nonneg_left hrBound hK
    _ ≤ K * (4 * Real.log x) := by
      apply mul_le_mul_of_nonneg_left _ hK
      linarith
    _ = 16 * (x : ℝ) * Real.log x ^ 2 / U := by
      dsimp [K]
      ring
    _ ≤ 32 * (x : ℝ) * Real.log x ^ 2 / U := by
      have hbase : 0 ≤ (x : ℝ) * Real.log x ^ 2 / U := by positivity
      calc
        16 * (x : ℝ) * Real.log x ^ 2 / U =
            16 * ((x : ℝ) * Real.log x ^ 2 / U) := by ring
        _ ≤ 32 * ((x : ℝ) * Real.log x ^ 2 / U) :=
          mul_le_mul_of_nonneg_right (by norm_num) hbase
        _ = 32 * (x : ℝ) * Real.log x ^ 2 / U := by ring

private lemma dirichletPerronCoefficientMass_twist_vonMangoldt_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    dirichletPerronCoefficientMass
        ((fun n : ℕ => chi n) *
          fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) sigma ≤
      ∑' n : ℕ,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma := by
  let f : ℕ → ℂ :=
    (fun n : ℕ => chi n) *
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ :=
    fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hf : LSeriesSummable f (sigma : ℂ) := by
    simpa [f] using
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hsigma
  have hg : LSeriesSummable g (sigma : ℂ) := by
    simpa [g] using
      ArithmeticFunction.LSeriesSummable_vonMangoldt hsigma
  have hcoeff (n : ℕ) : ‖f n‖ ≤ ‖g n‖ := by
    simp only [f, g, Pi.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (chi.norm_le_one (n : ZMod q)) (norm_nonneg _)).trans_eq
        (one_mul _)
  have hterm (n : ℕ) :
      ‖LSeries.term f (sigma : ℂ) n‖ ≤
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma := by
    calc
      ‖LSeries.term f (sigma : ℂ) n‖ ≤
          ‖LSeries.term g (sigma : ℂ) n‖ :=
        LSeries.norm_term_le _ (hcoeff n)
      _ = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma := by
        rw [LSeries.norm_term_eq]
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, if_false, g, Complex.ofReal_re]
          rw [Complex.norm_of_nonneg
            ArithmeticFunction.vonMangoldt_nonneg]
  have hpositive : Summable fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma := by
    exact hg.norm.congr fun n => by
      symm
      rw [LSeries.norm_term_eq]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false, g, Complex.ofReal_re]
        rw [Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact hf.norm.tsum_le_tsum hterm hpositive

/-- One natural constant, chosen before all arithmetic parameters, bounds the
absolute twisted von Mangoldt coefficient mass on the Perron line. -/
theorem
    exists_nat_dirichletPerronCoefficientMass_twist_vonMangoldt_le :
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ {q : ℕ} (chi : DirichletCharacter ℂ q)
        {x : ℕ}, 4 ≤ x →
          dirichletPerronCoefficientMass
              ((fun n : ℕ => chi n) *
                fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (1 + 1 / Real.log x) ≤
            B * Real.log x := by
  rcases exists_pos_vonMangoldt_tsum_lt_inv_sub_one_add with
    ⟨C, hC, hsource⟩
  let B : ℕ := ⌈C⌉₊ + 2
  refine ⟨B, by simp [B], ?_⟩
  intro q chi x hx
  have hxPos : 0 < x := by omega
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hxPos
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlogStrict : (1 : ℝ) < Real.log x := by
    calc
      (1 : ℝ) < 2 * Real.log 2 := by linarith
      _ = Real.log 4 := Real.log_four_eq.symm
      _ ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  let sigma : ℝ := 1 + 1 / Real.log x
  have hsigmaOne : 1 < sigma := by
    dsimp [sigma]
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have hsigmaTwo : sigma < 2 := by
    have hinv : 1 / Real.log x < 1 :=
      (div_lt_one (by linarith : 0 < Real.log x)).2 hlogStrict
    dsimp [sigma]
    linarith
  have hmass :=
    dirichletPerronCoefficientMass_twist_vonMangoldt_le chi hsigmaOne
  have hraw := hsource sigma hsigmaOne hsigmaTwo
  have hinverse : (sigma - 1)⁻¹ = Real.log x := by
    dsimp [sigma]
    field_simp [ne_of_gt (show 0 < Real.log x by linarith)]
    ring
  rw [hinverse] at hraw
  have hceil : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hlogOne : (1 : ℝ) ≤ Real.log x := hlogStrict.le
  have hprod :
      0 ≤ ((⌈C⌉₊ : ℝ) + 1) * (Real.log x - 1) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hlogOne)
  change dirichletPerronCoefficientMass
      ((fun n : ℕ => chi n) *
        fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) sigma ≤ _
  calc
    dirichletPerronCoefficientMass
        ((fun n : ℕ => chi n) *
          fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) sigma ≤
        ∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma := hmass
    _ ≤ Real.log x + C := hraw.le
    _ ≤ (B : ℝ) * Real.log x := by
      dsimp [B]
      push_cast
      nlinarith

end


end BoundedGaps.Maynard
