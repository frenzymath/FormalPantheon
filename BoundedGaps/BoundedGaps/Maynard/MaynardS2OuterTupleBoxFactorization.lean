import BoundedGaps.Maynard.ConcreteFractionalTupleBox
import BoundedGaps.Maynard.MaynardS2OuterCumulative

noncomputable section

/-!
# Finite S2 outer tuple-box factorization

The outer squarefree coefficient is a product measure on the independent
coordinate box.  This file records that exact finite identity separately from
the reciprocal-totient box machinery, since the two measures are not equal.
-/

namespace BoundedGaps.Maynard

open Finset
open scoped BigOperators

theorem maynardS2OuterSquarefreeAF_eq_zero_of_not_squarefree
    {W n : ℕ} (hn : ¬ Squarefree n) :
    maynardS2OuterSquarefreeAF W n = 0 := by
  unfold maynardS2OuterSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn
  simp [hmu]

theorem maynardS2OuterSquarefreeAF_eq_zero_of_not_coprime
    {W n : ℕ} (hcop : ¬ Nat.Coprime n W) :
    maynardS2OuterSquarefreeAF W n = 0 := by
  by_cases hn : n = 0
  · subst n
    exact (maynardS2OuterSquarefreeAF W).map_zero
  obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpMem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn
  unfold maynardS2OuterSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  rw [maynardS2OuterWeightAF,
    ArithmeticFunction.prodPrimeFactors_apply hn]
  have hprod : ∏ q ∈ n.primeFactors,
      (if q ∣ W then 0 else maynardS2OuterScalarWeight q) = 0 := by
    apply Finset.prod_eq_zero hpMem
    simp [hpW]
  simp [hprod]

theorem maynardS2OuterSquarefreeCoordinateSupport_sum_le_mean
    (W Q : ℕ) :
    (∑ n ∈ squarefreeCoprimeCoordinateSupport W Q,
      maynardS2OuterSquarefreeAF W n) ≤
      maynardS2OuterSquarefreeMean W Q := by
  unfold maynardS2OuterSquarefreeMean
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hnFull hnNot
    exact maynardS2OuterSquarefreeAF_nonneg W n

theorem maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean
    (W Q : ℕ) :
    (∑ n ∈ squarefreeCoprimeCoordinateSupport W Q,
      maynardS2OuterSquarefreeAF W n) =
      maynardS2OuterSquarefreeMean W Q := by
  unfold maynardS2OuterSquarefreeMean
  apply Finset.sum_subset
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hnFull hnNot
    by_cases hsq : Squarefree n
    · by_cases hcop : Nat.Coprime n W
      · exact False.elim (hnNot (Finset.mem_filter.mpr ⟨hnFull, hsq, hcop⟩))
      · rw [maynardS2OuterSquarefreeAF_eq_zero_of_not_coprime hcop]
    · rw [maynardS2OuterSquarefreeAF_eq_zero_of_not_squarefree hsq]

theorem maynardS2OuterSquarefreeTupleBox_sum_eq_prod
    {H : Finset ℕ} {W : ℕ} {Q : H → ℕ} :
    (∑ u ∈ squarefreeCoprimeTupleBox H W Q,
      ∏ h : H, maynardS2OuterSquarefreeAF W (u h)) =
      ∏ h : H, ∑ n ∈ squarefreeCoprimeCoordinateSupport W (Q h),
        maynardS2OuterSquarefreeAF W n := by
  unfold squarefreeCoprimeTupleBox
  exact (Finset.prod_univ_sum
    (fun h : H => squarefreeCoprimeCoordinateSupport W (Q h))
    (fun h : H => fun n => maynardS2OuterSquarefreeAF W n)).symm

theorem maynardS2OuterSquarefreeTupleBox_sum_le_prod_mean
    {H : Finset ℕ} {W : ℕ} {Q : H → ℕ} :
    (∑ u ∈ squarefreeCoprimeTupleBox H W Q,
      ∏ h : H, maynardS2OuterSquarefreeAF W (u h)) ≤
      ∏ h : H, maynardS2OuterSquarefreeMean W (Q h) := by
  rw [maynardS2OuterSquarefreeTupleBox_sum_eq_prod]
  apply Finset.prod_le_prod
  · intro h hh
    exact Finset.sum_nonneg fun n hn =>
      maynardS2OuterSquarefreeAF_nonneg W n
  · intro h hh
    exact maynardS2OuterSquarefreeCoordinateSupport_sum_le_mean W (Q h)

theorem maynardS2OuterSquarefreeTupleBox_sum_eq_prod_mean
    {H : Finset ℕ} {W : ℕ} {Q : H → ℕ} :
    (∑ u ∈ squarefreeCoprimeTupleBox H W Q,
      ∏ h : H, maynardS2OuterSquarefreeAF W (u h)) =
      ∏ h : H, maynardS2OuterSquarefreeMean W (Q h) := by
  rw [maynardS2OuterSquarefreeTupleBox_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro h hh
  exact maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean W (Q h)

end BoundedGaps.Maynard
