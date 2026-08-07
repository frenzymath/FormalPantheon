import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveConductorFibers

/-!
# Parseval on the Dirichlet-character group

This file proves the exact fixed-modulus character Parseval identity used in
the large-sieve reduction. The transform is indexed by unit residue classes,
so distinct natural indices occupying the same residue class are not
incorrectly treated as orthogonal. See SEM-443 and
MontgomeryVaughanLargeSieveDraft2021, Theorem 4.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- The inverse-character transform of a function on unit residue classes. -/
noncomputable def dirichletCharacterUnitTransform
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * b a

private theorem star_inv_dirichletCharacter_apply_unit
    {q : ℕ} (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    star (χ⁻¹ (a : ZMod q)) = χ (a : ZMod q) := by
  rw [MulChar.star_apply']
  simp

private theorem dirichletCharacter_map_inv_unit
    {q : ℕ} (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    χ ((a : ZMod q)⁻¹) = (χ (a : ZMod q))⁻¹ := by
  rw [show ((a : ZMod q)⁻¹) = (a⁻¹ : (ZMod q)ˣ) by
    exact ZMod.inv_coe_unit a]
  rw [← MulChar.coe_toUnitHom χ, ← MulChar.coe_toUnitHom χ]
  simp

private theorem sum_star_inv_char_mul_inv_char_unit
    {q : ℕ} [NeZero q] (a c : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q,
      star (χ⁻¹ (a : ZMod q)) * χ⁻¹ (c : ZMod q)) =
      if a = c then (q.totient : ℂ) else 0 := by
  simp_rw [star_inv_dirichletCharacter_apply_unit]
  simp_rw [MulChar.inv_apply_eq_inv']
  calc
    (∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q) * (χ (c : ZMod q))⁻¹) =
        ∑ χ : DirichletCharacter ℂ q,
          χ ((c : ZMod q)⁻¹) * χ (a : ZMod q) := by
      apply Finset.sum_congr rfl
      intro χ _hχ
      rw [dirichletCharacter_map_inv_unit]
      ring
    _ = if (c : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ c.isUnit (a : ZMod q)
    _ = if a = c then (q.totient : ℂ) else 0 := by
      congr 1
      exact propext (by
        simpa [eq_comm] using (Units.val_inj : (a : ZMod q) = c ↔ a = c))

private theorem star_dirichletCharacterUnitTransform
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    star (dirichletCharacterUnitTransform b χ) =
      ∑ a : (ZMod q)ˣ, star (b a) * star (χ⁻¹ (a : ZMod q)) := by
  unfold dirichletCharacterUnitTransform
  calc
    star (∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * b a) =
        ∑ a : (ZMod q)ˣ, star (χ⁻¹ (a : ZMod q) * b a) := by
      exact map_sum (starRingEnd ℂ) _ Finset.univ
    _ = ∑ a : (ZMod q)ˣ,
        star (b a) * star (χ⁻¹ (a : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [star_mul]

/-- Exact Parseval for the inverse-character transform on `(ZMod q)ˣ`. -/
theorem sum_norm_sq_dirichletCharacterUnitTransform
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖dirichletCharacterUnitTransform b χ‖ ^ 2) =
      (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖b a‖ ^ 2 := by
  have hcomplex :
      (∑ χ : DirichletCharacter ℂ q,
        star (dirichletCharacterUnitTransform b χ) *
          dirichletCharacterUnitTransform b χ) =
        (q.totient : ℂ) * ∑ a : (ZMod q)ˣ, star (b a) * b a := by
    simp_rw [star_dirichletCharacterUnitTransform]
    unfold dirichletCharacterUnitTransform
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    calc
      (∑ χ : DirichletCharacter ℂ q,
          ∑ a : (ZMod q)ˣ,
            ∑ c : (ZMod q)ˣ,
              (star (b a) * star (χ⁻¹ (a : ZMod q))) *
                (χ⁻¹ (c : ZMod q) * b c)) =
          ∑ a : (ZMod q)ˣ,
            ∑ c : (ZMod q)ˣ,
              ∑ χ : DirichletCharacter ℂ q,
                (star (b a) * star (χ⁻¹ (a : ZMod q))) *
                  (χ⁻¹ (c : ZMod q) * b c) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_comm]
      _ = ∑ a : (ZMod q)ˣ,
          ∑ c : (ZMod q)ˣ,
            (star (b a) * b c) *
              ∑ χ : DirichletCharacter ℂ q,
                star (χ⁻¹ (a : ZMod q)) * χ⁻¹ (c : ZMod q) := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro c _hc
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _hχ
        ring
      _ = ∑ a : (ZMod q)ˣ,
          ∑ c : (ZMod q)ˣ,
            (star (b a) * b c) *
              (if a = c then (q.totient : ℂ) else 0) := by
        simp_rw [sum_star_inv_char_mul_inv_char_unit]
      _ = ∑ a : (ZMod q)ˣ,
          (q.totient : ℂ) * (star (b a) * b a) := by
        apply Finset.sum_congr rfl
        intro a _ha
        simp
        ring
  rw [Complex.star_def] at hcomplex
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at hcomplex
  exact_mod_cast hcomplex

private theorem sum_norm_sq_primitiveCharacterUnitTransform_le_all
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ) :
    (∑ ψ : primitiveCharacters q,
      ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2) ≤
      ∑ χ : DirichletCharacter ℂ q,
        ‖dirichletCharacterUnitTransform b χ‖ ^ 2 := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.IsPrimitive))
    (by simp) (fun χ ↦ ‖dirichletCharacterUnitTransform b χ‖ ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (by intros; positivity)

/-- Restricting Parseval to primitive characters gives an inequality. -/
theorem sum_norm_sq_primitiveCharacterUnitTransform_le
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ) :
    (∑ ψ : primitiveCharacters q,
      ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖b a‖ ^ 2 := by
  rw [← sum_norm_sq_dirichletCharacterUnitTransform]
  exact sum_norm_sq_primitiveCharacterUnitTransform_le_all b

/-- The source weight `q / phi(q)` cancels the Parseval factor. -/
theorem weighted_sum_norm_sq_primitiveCharacterUnitTransform_le
    {q : ℕ} [NeZero q] (b : (ZMod q)ˣ → ℂ) :
    (q : ℝ) / (q.totient : ℝ) *
        ∑ ψ : primitiveCharacters q,
          ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2 ≤
      (q : ℝ) * ∑ a : (ZMod q)ˣ, ‖b a‖ ^ 2 := by
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  calc
    (q : ℝ) / (q.totient : ℝ) *
        ∑ ψ : primitiveCharacters q,
          ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2 ≤
        (q : ℝ) / (q.totient : ℝ) *
          ((q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖b a‖ ^ 2) := by
      gcongr
      exact sum_norm_sq_primitiveCharacterUnitTransform_le b
    _ = (q : ℝ) * ∑ a : (ZMod q)ˣ, ‖b a‖ ^ 2 := by
      field_simp

end

end BoundedGaps.Maynard
