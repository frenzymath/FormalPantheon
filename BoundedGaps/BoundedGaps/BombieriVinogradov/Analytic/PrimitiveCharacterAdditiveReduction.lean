import BoundedGaps.BombieriVinogradov.Analytic.MultiplicativeCharacterParseval
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum

/-!
# Reduction of primitive twists to additive sums

This file combines SEM-443 character Parseval with SEM-434's primitive Gauss
identity. It proves the exact fixed-modulus reduction used before the additive
large sieve; no varying-modulus large-sieve estimate is asserted here.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

private theorem sum_units_invCharacter_mul_stdAddChar_eq_sum_zmod
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    (∑ u : (ZMod q)ˣ,
      χ⁻¹ (u : ZMod q) * ZMod.stdAddChar ((u : ZMod q) * n)) =
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n) := by
  classical
  letI : Fintype (IsUnit.submonoid (ZMod q)) := Fintype.ofFinite _
  calc
    (∑ u : (ZMod q)ˣ,
        χ⁻¹ (u : ZMod q) * ZMod.stdAddChar ((u : ZMod q) * n)) =
        ∑ a : IsUnit.submonoid (ZMod q),
          χ⁻¹ (a : ZMod q) * ZMod.stdAddChar ((a : ZMod q) * n) := by
      apply Fintype.sum_equiv
        (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := ZMod q)).toEquiv
      intro u
      rfl
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        χ⁻¹ a * ZMod.stdAddChar (a * n) := by
      exact (Finset.sum_subtype
        (p := IsUnit) ((Finset.univ : Finset (ZMod q)).filter IsUnit)
        (by simp) (fun a ↦ χ⁻¹ a * ZMod.stdAddChar (a * n))).symm
    _ = ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n) := by
      apply Finset.sum_filter_of_ne
      intro a _ha hterm
      by_contra ha
      simp [MulChar.map_nonunit χ⁻¹ ha] at hterm

/-- The unit-group transform of additive sums is a Gauss sum times the
corresponding primitive character twist. -/
theorem dirichletCharacterUnitTransform_additive_eq_gaussSum_mul_twist
    {q : ℕ} [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ)
    (ψ : primitiveCharacters q) :
    dirichletCharacterUnitTransform
        (fun u ↦ ∑ n ∈ s,
          c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) ψ.1 =
      gaussSum ψ.1⁻¹ ZMod.stdAddChar *
        ∑ n ∈ s, c n * ψ.1 n := by
  unfold dirichletCharacterUnitTransform
  calc
    (∑ u : (ZMod q)ˣ,
        ψ.1⁻¹ (u : ZMod q) *
          ∑ n ∈ s,
            c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) =
        ∑ u : (ZMod q)ˣ,
          ∑ n ∈ s,
            ψ.1⁻¹ (u : ZMod q) *
              (c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
    _ = ∑ n ∈ s,
        ∑ u : (ZMod q)ˣ,
          ψ.1⁻¹ (u : ZMod q) *
            (c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ s, c n *
        ∑ u : (ZMod q)ˣ,
          ψ.1⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    _ = ∑ n ∈ s, c n *
        (ψ.1 (n : ZMod q) * gaussSum ψ.1⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [sum_units_invCharacter_mul_stdAddChar_eq_sum_zmod]
      rw [primitive_fourier_expansion (χ := ψ.1) ψ.2 (n : ZMod q)]
    _ = gaussSum ψ.1⁻¹ ZMod.stdAddChar *
        ∑ n ∈ s, c n * ψ.1 n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

/-- Fixed-modulus primitive character twists are bounded by the corresponding
unit-indexed additive sums. This is the algebraic input to the additive large
sieve. -/
theorem weighted_sum_norm_sq_primitiveTwists_le_unitAdditiveSums
    {q : ℕ} [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ) :
    (q : ℝ) / (q.totient : ℝ) *
        ∑ ψ : primitiveCharacters q,
          ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 ≤
      ∑ u : (ZMod q)ˣ,
        ‖∑ n ∈ s,
          c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))‖ ^ 2 := by
  let b : (ZMod q)ˣ → ℂ := fun u ↦
    ∑ n ∈ s, c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  have htransform (ψ : primitiveCharacters q) :
      ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2 =
        (q : ℝ) * ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
    have hψinv : ψ.1⁻¹.IsPrimitive := by
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
      exact ψ.2
    rw [dirichletCharacterUnitTransform_additive_eq_gaussSum_mul_twist]
    rw [norm_mul, mul_pow,
      norm_gaussSum_stdAddChar_of_isPrimitive ψ.1⁻¹ hψinv]
    rw [Real.sq_sqrt (Nat.cast_nonneg q)]
  have hsum :
      (∑ ψ : primitiveCharacters q,
        ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2) =
        (q : ℝ) *
          ∑ ψ : primitiveCharacters q,
            ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
    simp_rw [htransform, Finset.mul_sum]
  have hparseval := sum_norm_sq_primitiveCharacterUnitTransform_le b
  rw [div_mul_eq_mul_div, div_le_iff₀ hphi]
  calc
    (q : ℝ) *
        ∑ ψ : primitiveCharacters q,
          ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 =
        ∑ ψ : primitiveCharacters q,
          ‖dirichletCharacterUnitTransform b ψ.1‖ ^ 2 := hsum.symm
    _ ≤ (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2 := hparseval
    _ = (∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2) * (q.totient : ℝ) := by ring

end

end BoundedGaps.Maynard
