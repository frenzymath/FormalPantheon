import BoundedGaps.Maynard.MaynardS2RestrictedReindex
import BoundedGaps.Maynard.MaynardS1YDiagonal

noncomputable section

/-!
# Restricted S2 Y-diagonal

This file identifies the finite restricted inverse-totient quadratic
transform with Maynard's `y^(m)` diagonal. It corresponds to
Maynard2013v3, source lines 380--386.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2RestrictedYDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def maynardS2RestrictedYFromCoefficients
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) (u : H → ℕ) : ℝ :=
  (∏ h : H, (ArithmeticFunction.moebius (u h) : ℝ) *
    maynardS2G (u h)) *
    ∑ d ∈ D,
      if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
        lambda d / divisorTupleTotientProduct H d
      else 0

noncomputable def maynardS2RestrictedYDiagonalSum
    (H : Finset ℕ) (R W : ℕ)
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ u ∈ maynardDivisorTupleSupport H R W,
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W) lambda m u ^ 2 /
      ∏ h : H, (maynardS2G (u h) : ℝ)

theorem maynardS2RestrictedQuadraticTerm_eq_yDiagonalTerm
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} (m : H) {u : H → ℕ}
    (hu : IsMaynardDivisorTuple H R W u) :
    (∏ h : H, (maynardS2G (u h) : ℝ)) *
        (∑ d ∈ D,
          if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
            lambda d / divisorTupleTotientProduct H d
          else 0) ^ 2 =
      maynardS2RestrictedYFromCoefficients H D lambda m u ^ 2 /
        ∏ h : H, (maynardS2G (u h) : ℝ) := by
  classical
  let muU : ℝ := ∏ h : H,
    (ArithmeticFunction.moebius (u h) : ℝ)
  let gU : ℝ := ∏ h : H, (maynardS2G (u h) : ℝ)
  let S : ℝ := ∑ d ∈ D,
    if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
      lambda d / divisorTupleTotientProduct H d
    else 0
  have hprefactor :
      (∏ h : H, (ArithmeticFunction.moebius (u h) : ℝ) *
        maynardS2G (u h)) = muU * gU := by
    dsimp [muU, gU]
    exact Finset.prod_mul_distrib
  have hy : maynardS2RestrictedYFromCoefficients H D lambda m u =
      muU * gU * S := by
    unfold maynardS2RestrictedYFromCoefficients
    rw [hprefactor]
  have hmuSq : muU * muU = 1 := by
    dsimp [muU]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro h hh
    have hsq := (squarefree_iff_moebius_sq_eq_one (u h)).mp
      (hu.coordinate_squarefree h)
    exact_mod_cast (by simpa [pow_two] using hsq)
  change gU * S ^ 2 =
    maynardS2RestrictedYFromCoefficients H D lambda m u ^ 2 / gU
  by_cases hg : gU = 0
  · rw [hg]
    simp
  · apply (eq_div_iff hg).2
    rw [hy, pow_two]
    nlinarith [hmuSq]

theorem maynardS2RestrictedQuadraticTransform_eq_yDiagonal
    {H : Finset ℕ} {R W : ℕ} {lambda : (H → ℕ) → ℝ} (m : H) :
    maynardS2RestrictedQuadraticTransform H R
        (maynardDivisorTupleSupport H R W) lambda m =
      maynardS2RestrictedYDiagonalSum H R W lambda m := by
  classical
  unfold maynardS2RestrictedQuadraticTransform
    maynardS2RestrictedYDiagonalSum
  calc
    (∑ u ∈ maynardDivisorTupleBox H R,
        (∏ h : H, (maynardS2G (u h) : ℝ)) *
          (∑ d ∈ maynardDivisorTupleSupport H R W,
            if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
              lambda d / divisorTupleTotientProduct H d
            else 0) ^ 2) =
        ∑ u ∈ maynardDivisorTupleSupport H R W,
          (∏ h : H, (maynardS2G (u h) : ℝ)) *
            (∑ d ∈ maynardDivisorTupleSupport H R W,
              if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
                lambda d / divisorTupleTotientProduct H d
              else 0) ^ 2 := by
      symm
      apply Finset.sum_subset
      · intro u hu
        exact (mem_maynardDivisorTupleSupport_iff.mp hu).1
      · intro u huBox huNot
        have hinner :
            (∑ d ∈ maynardDivisorTupleSupport H R W,
              if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
                lambda d / divisorTupleTotientProduct H d
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          rw [if_neg]
          intro hud
          exact huNot (mem_maynardDivisorTupleSupport_iff.mpr ⟨huBox,
            isMaynardDivisorTuple_of_mem_box_of_dvd huBox
              (isMaynardDivisorTuple_of_mem_support hd) hud.1⟩)
        rw [hinner, zero_pow (by decide), mul_zero]
    _ = ∑ u ∈ maynardDivisorTupleSupport H R W,
          maynardS2RestrictedYFromCoefficients H
              (maynardDivisorTupleSupport H R W) lambda m u ^ 2 /
            ∏ h : H, (maynardS2G (u h) : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact maynardS2RestrictedQuadraticTerm_eq_yDiagonalTerm m
        (isMaynardDivisorTuple_of_mem_support hu)

end BoundedGaps.Maynard
