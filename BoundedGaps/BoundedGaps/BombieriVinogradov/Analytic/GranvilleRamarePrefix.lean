import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamareProposition
import Mathlib.Analysis.Complex.Norm

/-!
# Prefix forms of the Granville--Ramare estimate

The dyadic estimate is summed by strong induction without enlarging its
constant.  The final theorem is the coefficient-energy estimate used in
Akbary--Hambrook2013v2, equation (6.14), printed p. 23.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- GranvilleRamare1996, Proposition 10.1, in the natural prefix form used by
Akbary--Hambrook2013v2, Lemma 3.1(g), printed p. 8. -/
theorem sum_sq_vaughanFourthCoefficient_prefix_le
    {V : ℝ} (hV : 1 ≤ V) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
      (vaughanFourthCoefficient V n) ^ 2) ≤
      (4 / 3 : ℝ) * (X : ℝ) * (Real.log V + 3) ^ 2 := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hXZero : X = 0
      · subst X
        simp
      by_cases hXOne : X = 1
      · subst X
        have hLog : 0 ≤ Real.log V := Real.log_nonneg hV
        have hCoefficient : vaughanFourthCoefficient V 1 = 1 := by
          unfold vaughanFourthCoefficient
          rw [Nat.divisors_one]
          have hFilter :
              ({1} : Finset ℕ).filter (fun d : ℕ => (d : ℝ) ≤ V) = {1} := by
            apply Finset.filter_eq_self.mpr
            intro d hd
            simp only [Finset.mem_singleton] at hd
            subst d
            simpa only [Nat.cast_one] using hV
          rw [hFilter]
          simp
        norm_num [hCoefficient]
        nlinarith [sq_nonneg (Real.log V)]
      have hXTwo : 2 ≤ X := by omega
      have hHalfLt : X / 2 < X :=
        Nat.div_lt_self (Nat.zero_lt_of_lt hXTwo) (Nat.le_refl 2)
      have hLower := ih (X / 2) hHalfLt
      have hHalfReal : (1 : ℝ) ≤ (X : ℝ) / 2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        exact_mod_cast hXTwo
      have hUpper := sum_sq_vaughanFourthCoefficient_dyadic_le
        (N := (X : ℝ) / 2) (V := V) hHalfReal hV
      have hFloorHalf : ⌊(X : ℝ) / 2⌋₊ = X / 2 := by
        simpa using (Nat.floor_div_natCast (K := ℝ) (X : ℝ) 2)
      have hTwiceHalf : (2 : ℝ) * ((X : ℝ) / 2) = X := by ring
      rw [hFloorHalf, hTwiceHalf, Nat.floor_natCast] at hUpper
      have hHalfLe : X / 2 ≤ X := Nat.div_le_self X 2
      have hDisjoint :
          Disjoint (Finset.Ioc 0 (X / 2)) (Finset.Ioc (X / 2) X) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      have hSplit :
          (∑ n ∈ Finset.Ioc 0 X,
            (vaughanFourthCoefficient V n) ^ 2) =
            (∑ n ∈ Finset.Ioc 0 (X / 2),
              (vaughanFourthCoefficient V n) ^ 2) +
            ∑ n ∈ Finset.Ioc (X / 2) X,
              (vaughanFourthCoefficient V n) ^ 2 := by
        rw [← Finset.sum_union hDisjoint,
          Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hHalfLe]
      have hLength :
          ((X / 2 : ℕ) : ℝ) + (X : ℝ) / 2 ≤ (X : ℝ) := by
        have hFloorLe : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 :=
          Nat.cast_div_le
        linarith
      have hFactorNonneg :
          0 ≤ (4 / 3 : ℝ) * (Real.log V + 3) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      rw [hSplit]
      calc
        (∑ n ∈ Finset.Ioc 0 (X / 2),
            (vaughanFourthCoefficient V n) ^ 2) +
            ∑ n ∈ Finset.Ioc (X / 2) X,
              (vaughanFourthCoefficient V n) ^ 2 ≤
            (4 / 3 : ℝ) * ((X / 2 : ℕ) : ℝ) *
                (Real.log V + 3) ^ 2 +
              (4 / 3 : ℝ) * ((X : ℝ) / 2) *
                (Real.log V + 3) ^ 2 := add_le_add hLower hUpper
        _ = ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) *
              (((X / 2 : ℕ) : ℝ) + (X : ℝ) / 2) := by ring
        _ ≤ ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) * (X : ℝ) :=
          mul_le_mul_of_nonneg_left hLength hFactorNonneg
        _ = (4 / 3 : ℝ) * (X : ℝ) * (Real.log V + 3) ^ 2 := by ring

/-- The real-endpoint prefix obtained by taking the natural floor. -/
theorem sum_sq_vaughanFourthCoefficient_realPrefix_le
    {X V : ℝ} (hX : 1 ≤ X) (hV : 1 ≤ V) :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (vaughanFourthCoefficient V n) ^ 2) ≤
      (4 / 3 : ℝ) * X * (Real.log V + 3) ^ 2 := by
  have hPrefix := sum_sq_vaughanFourthCoefficient_prefix_le hV ⌊X⌋₊
  have hFloor : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X :=
    Nat.floor_le (zero_le_one.trans hX)
  have hFactorNonneg :
      0 ≤ (4 / 3 : ℝ) * (Real.log V + 3) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  calc
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        (vaughanFourthCoefficient V n) ^ 2) ≤
        (4 / 3 : ℝ) * ((⌊X⌋₊ : ℕ) : ℝ) *
          (Real.log V + 3) ^ 2 := hPrefix
    _ = ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) *
          ((⌊X⌋₊ : ℕ) : ℝ) := by ring
    _ ≤ ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) * X :=
      mul_le_mul_of_nonneg_left hFloor hFactorNonneg
    _ = (4 / 3 : ℝ) * X * (Real.log V + 3) ^ 2 := by ring

/-- Akbary--Hambrook2013v2, equation (6.14), with its strict lower cutoff
retained on the left. -/
theorem sum_norm_sq_vaughanFourthCoefficient_Ioc_le
    {V : ℝ} {x M : ℕ} (hV : 1 ≤ V) (hM : 0 < M) :
    (∑ k ∈ (Finset.Ioc 0 (x / M)).filter
      (fun k : ℕ => V < (k : ℝ)),
      ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) ≤
      4 * (x : ℝ) / (3 * (M : ℝ)) *
        (Real.log (Real.exp 3 * V)) ^ 2 := by
  have hSubset :
      (Finset.Ioc 0 (x / M)).filter (fun k : ℕ => V < (k : ℝ)) ⊆
        Finset.Ioc 0 (x / M) := Finset.filter_subset _ _
  have hPrefix := sum_sq_vaughanFourthCoefficient_prefix_le hV (x / M)
  have hRestricted :
      (∑ k ∈ (Finset.Ioc 0 (x / M)).filter
          (fun k : ℕ => V < (k : ℝ)),
          ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) ≤
        ∑ k ∈ Finset.Ioc 0 (x / M),
          (vaughanFourthCoefficient V k) ^ 2 := by
    calc
      (∑ k ∈ (Finset.Ioc 0 (x / M)).filter
          (fun k : ℕ => V < (k : ℝ)),
          ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) =
          ∑ k ∈ (Finset.Ioc 0 (x / M)).filter
            (fun k : ℕ => V < (k : ℝ)),
            (vaughanFourthCoefficient V k) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ k ∈ Finset.Ioc 0 (x / M),
            (vaughanFourthCoefficient V k) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
        intro k hk hNot
        exact sq_nonneg _
  have hQuotient :
      (((x / M : ℕ) : ℝ)) ≤ (x : ℝ) / (M : ℝ) :=
    Nat.cast_div_le
  have hFactorNonneg :
      0 ≤ (4 / 3 : ℝ) * (Real.log V + 3) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hLog : Real.log (Real.exp 3 * V) = Real.log V + 3 := by
    rw [Real.log_mul (Real.exp_ne_zero 3) (ne_of_gt (zero_lt_one.trans_le hV)),
      Real.log_exp]
    ring
  calc
    (∑ k ∈ (Finset.Ioc 0 (x / M)).filter
        (fun k : ℕ => V < (k : ℝ)),
        ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) ≤
        ∑ k ∈ Finset.Ioc 0 (x / M),
          (vaughanFourthCoefficient V k) ^ 2 := hRestricted
    _ ≤ (4 / 3 : ℝ) * (((x / M : ℕ) : ℝ)) *
          (Real.log V + 3) ^ 2 := hPrefix
    _ = ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) *
          (((x / M : ℕ) : ℝ)) := by ring
    _ ≤ ((4 / 3 : ℝ) * (Real.log V + 3) ^ 2) *
          ((x : ℝ) / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hQuotient hFactorNonneg
    _ = 4 * (x : ℝ) / (3 * (M : ℝ)) *
          (Real.log (Real.exp 3 * V)) ^ 2 := by
      rw [hLog]
      have hMReal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp [hMReal]

end

end BoundedGaps.Maynard
