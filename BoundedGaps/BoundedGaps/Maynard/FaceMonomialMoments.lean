import BoundedGaps.Maynard.FaceDecomposition

/-!
# Inner moments on Maynard faces

The zero-extended quadratic monomial is integrated in the omitted coordinate.
Its support becomes the residual interval, the quadratic power is expanded by
the binomial theorem, and the resulting terms are evaluated by the scaled beta
integral.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def faceSupportedMonomial {n : ℕ} (m : Fin (n + 1)) (b c : ℕ)
    (t : maynardFaceIndex (n + 1) m → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if maynardInsertCoordinate m x t ∈ maynardSimplex (n + 1) then
    (1 - ∑ i, maynardInsertCoordinate m x t i) ^ b *
      (∑ i, (maynardInsertCoordinate m x t i) ^ 2) ^ c else 0

theorem faceSupportedMonomial_inner_formula {n : ℕ}
    (m : Fin (n + 1)) (b c : ℕ)
    (t : maynardFaceIndex (n + 1) m → ℝ)
    (ht : t ∈ maynardFaceSimplex m) :
    (∫ x in Set.Icc (0 : ℝ) 1, faceSupportedMonomial m b c t x) =
      ∑ cp ∈ Finset.range (c + 1),
        (((Nat.choose c cp : ℚ) * Nat.factorial b *
            Nat.factorial (2 * c - 2 * cp) /
          Nat.factorial (b + 2 * c - 2 * cp + 1) : ℚ) : ℝ) *
          (1 - ∑ j, t j) ^ (b + 2 * c - 2 * cp + 1) *
          (∑ j, (t j) ^ 2) ^ cp := by
  let r : ℝ := 1 - ∑ j, t j
  let q : ℝ := ∑ j, (t j) ^ 2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [ht.2]
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hs : 0 ≤ ∑ j, t j := Finset.sum_nonneg (fun j hj => ht.1 j)
    linarith
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      faceSupportedMonomial m b c t x =
        (Set.Icc (0 : ℝ) r).indicator
          (fun x => (r - x) ^ b * (q + x ^ 2) ^ c) x := by
    by_cases hxr : x ∈ Set.Icc (0 : ℝ) r
    · have hs := (insert_mem_simplex_iff m x t ht).2 hxr
      simp only [faceSupportedMonomial, Set.indicator_of_mem hxr, hs]
      rw [sum_insertCoordinate, sq_sum_insertCoordinate]
      dsimp [r, q]
      ring_nf
    · have hs := (insert_mem_simplex_iff m x t ht).not.mpr hxr
      simp [faceSupportedMonomial, Set.indicator, hxr, hs]
  have hsubset : Set.Icc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hr1⟩
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, faceSupportedMonomial m b c t x) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          (Set.Icc (0 : ℝ) r).indicator
            (fun x => (r - x) ^ b * (q + x ^ 2) ^ c) x := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hpoint
    _ = ∫ x in Set.Icc (0 : ℝ) r,
          (r - x) ^ b * (q + x ^ 2) ^ c := by
      have hzero := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (s := Set.Icc (0 : ℝ) r) (t := Set.Icc (0 : ℝ) 1)
        (μ := volume)
        (f := (Set.Icc (0 : ℝ) r).indicator
          (fun x => (r - x) ^ b * (q + x ^ 2) ^ c))
        measurableSet_Icc hsubset
        (fun x hx => by simp [Set.indicator, hx.2])
      calc
        _ = ∫ x in Set.Icc (0 : ℝ) r,
            (Set.Icc (0 : ℝ) r).indicator
              (fun x => (r - x) ^ b * (q + x ^ 2) ^ c) x := hzero
        _ = _ := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          simp [Set.indicator, hx]
    _ = _ := by
      by_cases hr : r = 0
      · subst r
        rw [hr]
        simp
      · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
        have hexpand (x : ℝ) :
            (q + x ^ 2) ^ c =
              ∑ cp ∈ Finset.range (c + 1),
                (Nat.choose c cp : ℝ) * q ^ cp *
                  x ^ (2 * (c - cp)) := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro cp hcp
          rw [pow_mul]
          ring
        rw [show (fun x : ℝ => (r - x) ^ b * (q + x ^ 2) ^ c) =
            (fun x => ∑ cp ∈ Finset.range (c + 1),
              (Nat.choose c cp : ℝ) *
                (q ^ cp * x ^ (2 * (c - cp)) * (r - x) ^ b)) by
          funext x
          rw [hexpand]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro cp hcp
          ring]
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro cp hcp
          rw [show (fun x : ℝ =>
              (Nat.choose c cp : ℝ) *
                (q ^ cp * x ^ (2 * (c - cp)) * (r - x) ^ b)) =
              (fun x => (Nat.choose c cp : ℝ) * q ^ cp *
                (x ^ (2 * (c - cp)) * (r - x) ^ b)) by
            funext x
            ring]
          have hcpC : cp ≤ c := by
            have := Finset.mem_range.mp hcp
            omega
          rw [MeasureTheory.integral_const_mul]
          rw [betaNatIntegral_scaled (2 * (c - cp)) b hrpos]
          have htwo : 2 * (c - cp) = 2 * c - 2 * cp := by omega
          have hexp : 2 * c - 2 * cp + b + 1 =
              b + 2 * c - 2 * cp + 1 := by omega
          rw [htwo, hexp]
          dsimp [r, q]
          push_cast
          ring
        · intro cp hcp
          have hcont : Continuous (fun x : ℝ =>
              (Nat.choose c cp : ℝ) *
                (q ^ cp * x ^ (2 * (c - cp)) * (r - x) ^ b)) := by
            fun_prop
          exact hcont.integrableOn_Icc

end
end BoundedGaps.Maynard
