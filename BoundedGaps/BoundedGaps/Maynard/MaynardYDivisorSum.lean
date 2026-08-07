import BoundedGaps.Maynard.MaynardS1GlobalCrossReindex

noncomputable section

/-!
# Supported divisor sums from the forward Y transform

The forward transform is solved for its divisor sum, including lower tuples
outside Maynard support.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

theorem supportedDivisorSum_eq_mu_mul_y_div_totient
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {r : H → ℕ} (hrPos : ∀ h : H, 0 < r h) :
    (∑ d ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, r h ∣ d h then
          maynardCoefficientFromY H R W y d /
            (divisorTupleProduct H d : ℝ)
        else 0) =
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)) * y r /
        ∏ h : H, (Nat.totient (r h) : ℝ) := by
  classical
  by_cases hr : IsMaynardDivisorTuple H R W r
  · let muR : ℝ := ∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)
    let phiR : ℝ := ∏ h : H, (Nat.totient (r h) : ℝ)
    let S : ℝ := ∑ d ∈ maynardDivisorTupleSupport H R W,
      if ∀ h : H, r h ∣ d h then
        maynardCoefficientFromY H R W y d /
          (divisorTupleProduct H d : ℝ)
      else 0
    have hsupportBox := sum_maynardSupport_eq_box_for_coefficientFromY hy r
    have hforward := maynardYFromCoefficients_maynardCoefficientFromY hy hr
    unfold maynardYFromCoefficients at hforward
    rw [← hsupportBox] at hforward
    have hprefactor :
        (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
            Nat.totient (r h)) = muR * phiR := by
      dsimp [muR, phiR]
      exact Finset.prod_mul_distrib
    have hforward' : muR * phiR * S = y r := by
      rw [← hprefactor]
      exact hforward
    have hmuSq : muR * muR = 1 := by
      dsimp [muR]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro h hh
      have hsq := (squarefree_iff_moebius_sq_eq_one (r h)).mp
        (hr.coordinate_squarefree h)
      exact_mod_cast (by simpa [pow_two] using hsq)
    have hphiNe : phiR ≠ 0 := by
      apply ne_of_gt
      dsimp [phiR]
      apply Finset.prod_pos
      intro h hh
      exact_mod_cast Nat.totient_pos.mpr (hrPos h)
    change S = muR * y r / phiR
    apply (eq_div_iff hphiNe).2
    rw [← hforward']
    calc
      S * phiR = (muR * muR) * (S * phiR) := by rw [hmuSq, one_mul]
      _ = muR * (muR * phiR * S) := by ring
  · have hyr : y r = 0 := by
      by_contra hyr
      exact hr (hy r hyr)
    have hsum :
        (∑ d ∈ maynardDivisorTupleSupport H R W,
          if ∀ h : H, r h ∣ d h then
            maynardCoefficientFromY H R W y d /
              (divisorTupleProduct H d : ℝ)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [if_neg]
      intro hrd
      have hdSupport := isMaynardDivisorTuple_of_mem_support hd
      have hdProdPos : 0 < divisorTupleProduct H d :=
        Nat.pos_of_ne_zero hdSupport.2.2.ne_zero
      have hrBox : r ∈ maynardDivisorTupleBox H R := by
        apply mem_maynardDivisorTupleBox_iff.mpr
        intro h
        have hdLe : d h ≤ divisorTupleProduct H d :=
          Nat.le_of_dvd hdProdPos (divisorTupleCoordinate_dvd_product d h)
        have hdPos : 0 < d h :=
          Nat.pos_of_ne_zero (hdSupport.coordinate_squarefree h).ne_zero
        have hrLe : r h ≤ d h := Nat.le_of_dvd hdPos (hrd h)
        exact ⟨hrPos h, lt_of_le_of_lt (hrLe.trans hdLe) hdSupport.1⟩
      exact hr (isMaynardDivisorTuple_of_mem_box_of_dvd hrBox hdSupport hrd)
    rw [hsum, hyr]
    simp

end BoundedGaps.Maynard
