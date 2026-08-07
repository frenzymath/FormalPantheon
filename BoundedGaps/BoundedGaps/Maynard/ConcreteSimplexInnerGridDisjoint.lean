import BoundedGaps.Maynard.ConcreteSimplexInnerGrid

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

theorem disjoint_squarefreeCoprimeCoordinateShell_of_support_le
    {W Qlo₁ Qhi₁ Qlo₂ Qhi₂ : ℕ} (hQ : Qhi₁ ≤ Qlo₂) :
    Disjoint (squarefreeCoprimeCoordinateShell W Qlo₁ Qhi₁)
      (squarefreeCoprimeCoordinateShell W Qlo₂ Qhi₂) := by
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  have hnUpper := Finset.mem_sdiff.mp hn₁ |>.1
  have hnNotLower := Finset.mem_sdiff.mp hn₂ |>.2
  exact hnNotLower (squarefreeCoprimeCoordinateSupport_subset hQ hnUpper)

theorem disjoint_squarefreeCoprimeTupleShell_of_coordinate
    {H : Finset ℕ} {W : ℕ} {Qlo₁ Qhi₁ Qlo₂ Qhi₂ : H → ℕ}
    {h : H}
    (hdis : Disjoint
      (squarefreeCoprimeCoordinateShell W (Qlo₁ h) (Qhi₁ h))
      (squarefreeCoprimeCoordinateShell W (Qlo₂ h) (Qhi₂ h))) :
    Disjoint (squarefreeCoprimeTupleShell H W Qlo₁ Qhi₁)
      (squarefreeCoprimeTupleShell H W Qlo₂ Qhi₂) := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  have hu₁' := Fintype.mem_piFinset.mp hu₁ h
  have hu₂' := Fintype.mem_piFinset.mp hu₂ h
  exact Finset.disjoint_left.mp hdis hu₁' hu₂'

theorem eventually_engelsmaFractionalGridShells_pairwise_disjoint
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ j k : H → ℕ, j ≠ k →
        Disjoint
          (engelsmaFractionalTupleShell H alpha
            (fractionalGridLower m j) (fractionalGridUpper m j) N)
          (engelsmaFractionalTupleShell H alpha
            (fractionalGridLower m k) (fractionalGridUpper m k) N) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro j k hne
  have hcoord : ∃ h : H, j h ≠ k h := by
    by_contra hnone
    apply hne
    funext h
    by_contra hdiff
    exact hnone ⟨h, hdiff⟩
  obtain ⟨h, hneH⟩ := hcoord
  by_cases hjk : j h < k h
  · have hjkSucc : j h + 1 ≤ k h := Nat.succ_le_of_lt hjk
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hfrac : fractionalGridUpper m j h ≤
        fractionalGridLower m k h := by
      unfold fractionalGridUpper fractionalGridLower
      apply (div_le_div_iff_of_pos_right hmReal).2
      exact_mod_cast hjkSucc
    have hexp : alpha * fractionalGridUpper m j h ≤
        alpha * fractionalGridLower m k h :=
      mul_le_mul_of_nonneg_left hfrac halpha.le
    have hRmono : engelsmaMaynardRadius
          (alpha * fractionalGridUpper m j h) N ≤
        engelsmaMaynardRadius
          (alpha * fractionalGridLower m k h) N := by
      unfold engelsmaMaynardRadius maynardDivisorCutoff
      apply Nat.floor_mono
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ N - 1 by omega)
      · exact hexp
    apply disjoint_squarefreeCoprimeTupleShell_of_coordinate
      (h := h)
    apply disjoint_squarefreeCoprimeCoordinateShell_of_support_le
    simpa [engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell] using hRmono
  · have hkj : k h < j h := lt_of_le_of_ne (Nat.le_of_not_gt hjk)
      (Ne.symm hneH)
    have hkji := Nat.succ_le_of_lt hkj
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hfrac : fractionalGridUpper m k h ≤
        fractionalGridLower m j h := by
      unfold fractionalGridUpper fractionalGridLower
      apply (div_le_div_iff_of_pos_right hmReal).2
      exact_mod_cast hkji
    have hexp := mul_le_mul_of_nonneg_left hfrac halpha.le
    have hRmono : engelsmaMaynardRadius
          (alpha * fractionalGridUpper m k h) N ≤
        engelsmaMaynardRadius
          (alpha * fractionalGridLower m j h) N := by
      unfold engelsmaMaynardRadius maynardDivisorCutoff
      apply Nat.floor_mono
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ N - 1 by omega)
      · exact hexp
    have hdisReverse : Disjoint
        (engelsmaFractionalTupleShell H alpha
          (fractionalGridLower m k) (fractionalGridUpper m k) N)
        (engelsmaFractionalTupleShell H alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N) := by
      apply disjoint_squarefreeCoprimeTupleShell_of_coordinate (h := h)
      apply disjoint_squarefreeCoprimeCoordinateShell_of_support_le
      simpa [engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell] using hRmono
    exact hdisReverse.symm

theorem eventually_engelsmaSimplexInnerGridShells_pairwise_disjoint
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ fractionalSimplexInnerGridIndex H m,
      ∀ k ∈ fractionalSimplexInnerGridIndex H m, j ≠ k →
        Disjoint
          (engelsmaFractionalTupleShell H alpha
            (fractionalGridLower m j) (fractionalGridUpper m j) N)
          (engelsmaFractionalTupleShell H alpha
            (fractionalGridLower m k) (fractionalGridUpper m k) N) := by
  have hdis := eventually_engelsmaFractionalGridShells_pairwise_disjoint
    (H := H) halpha hm
  filter_upwards [hdis] with N hdisN j hj k hk hne
  exact hdisN j k hne

def engelsmaSimplexInnerGridSupportMass
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaSimplexInnerGridSupport H alpha m N,
    reciprocalTotientTupleWeight H u

theorem eventually_engelsmaSimplexInnerGridSupportMass_eq_stepMass
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaSimplexInnerGridSupportMass H alpha m N =
        ∑ j ∈ fractionalSimplexInnerGridIndex H m,
          engelsmaFractionalTupleShellMass H alpha
            (fractionalGridLower m j) (fractionalGridUpper m j) N := by
  have hdis := eventually_engelsmaSimplexInnerGridShells_pairwise_disjoint
    (H := H) halpha hm
  filter_upwards [hdis] with N hdisN
  unfold engelsmaSimplexInnerGridSupportMass
    engelsmaSimplexInnerGridSupport
  rw [Finset.sum_biUnion]
  · rfl
  · intro j hj k hk hne
    exact hdisN j hj k hk hne

end BoundedGaps.Maynard
