import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum
import BoundedGaps.BombieriVinogradov.Analytic.StandardAddCharInterval

/-!
# Primitive character sums on translated integer intervals

This file composes the audited primitive Fourier expansion with the translated
standard-character interval estimate. The sharp reciprocal-sine aggregate is
left to a later owner.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_zmod_erase_zero_eq_sum_Ico_val
    {q : ℕ} [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) =
      ∑ a ∈ Finset.Ico 1 q, f (a : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    exact Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha0, a.val_lt⟩
  · exact (ZMod.val_injective q).injOn
  · intro b hb
    have hbmem := Finset.mem_Ico.mp hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      apply (ZMod.val_ne_zero _).mp
      rw [ZMod.val_cast_of_lt hbmem.2]
      exact Nat.ne_of_gt hbmem.1
    · exact ZMod.val_cast_of_lt hbmem.2
  · intro a ha
    rw [ZMod.natCast_zmod_val]

/-- Summing the primitive Fourier expansion over a translated integer interval
and commuting the two finite sums. -/
theorem sum_dirichletCharacter_Ioc_eq_fourier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a : ZMod q, chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hpoint (n : ℤ) :
      chi (n : ZMod q) =
        (∑ a : ZMod q,
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
    exact primitive_fourier_expansion_div chi hchi (n : ZMod q)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ((∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
            gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      rw [Finset.sum_div]
    _ = (∑ a : ZMod q, ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]

/-- At modulus greater than one, the zero Fourier frequency has zero character
coefficient and may be erased exactly. -/
theorem sum_dirichletCharacter_Ioc_eq_fourier_erase_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hzero : chi⁻¹ (0 : ZMod q) = 0 :=
    DirichletCharacter.map_zero' chi⁻¹ (Nat.ne_of_gt hq)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier chi hchi M N
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
      simp [hzero]

/-- The erased nonzero Fourier frequencies, written as their canonical natural
representatives `1 ≤ a < q`. -/
theorem sum_dirichletCharacter_Ioc_eq_nat_fourier
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier_erase_zero hq chi hchi M N
    _ = (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      exact sum_zmod_erase_zero_eq_sum_Ico_val
        (f := fun a : ZMod q => chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q)))

/-- Davenport's primitive-character interval envelope before the sharp
reciprocal-sine aggregate. -/
theorem norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
      (∑ a ∈ Finset.Ico 1 q,
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
        Real.sqrt q := by
  classical
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgaussNorm : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt q :=
    norm_gaussSum_stdAddChar_of_isPrimitive chi⁻¹ hchiInv
  have hnumerator :
      ‖∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤
        ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          ‖chi⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
              ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haIco := Finset.mem_Ico.mp ha
        have ha0 : (a : ZMod q) ≠ 0 := by
          apply (ZMod.val_ne_zero (a : ZMod q)).mp
          rw [ZMod.val_cast_of_lt haIco.2]
          exact Nat.ne_of_gt haIco.1
        have hinterval := norm_sum_stdAddChar_Ioc_le_inv_sin
          (q := q) (a := (a : ZMod q)) ha0 M N
        rw [ZMod.val_cast_of_lt haIco.2] at hinterval
        calc
          ‖chi⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ =
              ‖chi⁻¹ (a : ZMod q)‖ *
                ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                  ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
            norm_mul _ _
          _ ≤ 1 * (Real.sin
                (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
            mul_le_mul (DirichletCharacter.norm_le_one chi⁻¹ (a : ZMod q))
              hinterval (norm_nonneg _) zero_le_one
          _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  rw [sum_dirichletCharacter_Ioc_eq_nat_fourier hq chi hchi M N,
    norm_div, hgaussNorm]
  exact div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg q)

end BoundedGaps.Maynard
