import BoundedGaps.Maynard.ConcreteFractionalTupleBoxSimplex

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

/-!
This project-local rectangle-shell decomposition makes the repeated partial
summation behind `Maynard2013v3`, printed Section 6,
`lmm:S1Summation2`/`eq:S1BasicExpression` (source lines 475--491), explicit.
Semantic review: `SEM-212`.
-/

def squarefreeCoprimeCoordinateShell (W Qlo Qhi : ℕ) : Finset ℕ :=
  squarefreeCoprimeCoordinateSupport W Qhi \
    squarefreeCoprimeCoordinateSupport W Qlo

theorem squarefreeCoprimeCoordinateSupport_subset
    {W Qlo Qhi : ℕ} (hQ : Qlo ≤ Qhi) :
    squarefreeCoprimeCoordinateSupport W Qlo ⊆
      squarefreeCoprimeCoordinateSupport W Qhi := by
  unfold squarefreeCoprimeCoordinateSupport at *
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnIcc := Finset.mem_Icc.mp hnData.1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hnIcc.1, hnIcc.2.trans hQ⟩, hnData.2⟩

theorem squarefreeCoprimeCoordinateShell_sum_eq_sub
    {W Qlo Qhi : ℕ} (hQ : Qlo ≤ Qhi) :
    (∑ n ∈ squarefreeCoprimeCoordinateShell W Qlo Qhi,
      (1 : ℝ) / Nat.totient n) =
      squarefreeCoprimeInvTotientMean W Qhi -
        squarefreeCoprimeInvTotientMean W Qlo := by
  unfold squarefreeCoprimeCoordinateShell
  rw [← squarefreeCoprimeCoordinateSupport_sum W Qhi,
    ← squarefreeCoprimeCoordinateSupport_sum W Qlo]
  exact Finset.sum_sdiff_eq_sub
    (squarefreeCoprimeCoordinateSupport_subset hQ)

def squarefreeCoprimeTupleShell
    (H : Finset ℕ) (W : ℕ) (Qlo Qhi : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun h =>
    squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h)

theorem reciprocalTotientTupleWeight_sum_squarefreeCoprimeTupleShell_eq
    {H : Finset ℕ} {W : ℕ} {Qlo Qhi : H → ℕ}
    (hQ : ∀ h : H, Qlo h ≤ Qhi h) :
    (∑ u ∈ squarefreeCoprimeTupleShell H W Qlo Qhi,
      reciprocalTotientTupleWeight H u) =
      ∏ h : H,
        (squarefreeCoprimeInvTotientMean W (Qhi h) -
          squarefreeCoprimeInvTotientMean W (Qlo h)) := by
  rw [squarefreeCoprimeTupleShell,
    reciprocalTotientTupleWeight_sum_pi_eq_prod]
  apply Finset.prod_congr rfl
  intro h hh
  exact squarefreeCoprimeCoordinateShell_sum_eq_sub (hQ h)

def engelsmaFractionalTupleShell
    (H : Finset ℕ) (alpha : ℝ) (beta gamma : H → ℝ) (N : ℕ) :
    Finset (H → ℕ) :=
  squarefreeCoprimeTupleShell H (engelsmaMaynardModulus N)
    (fun h => engelsmaMaynardRadius (alpha * beta h) N)
    (fun h => engelsmaMaynardRadius (alpha * gamma h) N)

def engelsmaFractionalTupleShellMass
    (H : Finset ℕ) (alpha : ℝ) (beta gamma : H → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaFractionalTupleShell H alpha beta gamma N,
    reciprocalTotientTupleWeight H u

def normalizedEngelsmaFractionalTupleShellMass
    (H : Finset ℕ) (alpha : ℝ) (beta gamma : H → ℝ) (N : ℕ) : ℝ :=
  engelsmaFractionalTupleShellMass H alpha beta gamma N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

theorem tendsto_engelsmaSquarefreeMean_fractionalRadius_interval
    {alpha beta gamma : ℝ} (halpha : 0 < alpha)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : gamma ∈ Set.Icc (0 : ℝ) 1)
    (horder : beta ≤ gamma) :
    Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * gamma) N) -
        squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (gamma - beta)) := by
  have hgammaT := tendsto_engelsmaSquarefreeMean_fractionalRadius_nonneg
    halpha hgamma.1
  have hbetaT := tendsto_engelsmaSquarefreeMean_fractionalRadius_nonneg
    halpha hbeta.1
  have hdiff := hgammaT.sub hbetaT
  apply hdiff.congr'
  have hmul : alpha * beta ≤ alpha * gamma :=
    mul_le_mul_of_nonneg_left horder halpha.le
  filter_upwards [eventually_engelsmaMaynardRadius_mono_exponent hmul] with
      N hQ
  rw [sub_div]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem tendsto_normalizedEngelsmaFractionalTupleShellMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta gamma : H → ℝ)
    (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ h, gamma h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ h, beta h ≤ gamma h) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaFractionalTupleShellMass H alpha beta gamma N)
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * gamma h) N) -
        squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (gamma h - beta h)) := by
    intro h
    exact tendsto_engelsmaSquarefreeMean_fractionalRadius_interval halpha
      (hbeta h) (hgamma h) (horder h)
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        (squarefreeCoprimeInvTotientMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * gamma h) N) -
          squarefreeCoprimeInvTotientMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta h) N)) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
    apply tendsto_finsetProd Finset.univ
    intro h hh
    exact hcoord h
  apply hprod.congr'
  have horderEvent : ∀ᶠ N : ℕ in atTop,
      ∀ h : H,
        engelsmaMaynardRadius (alpha * beta h) N ≤
          engelsmaMaynardRadius (alpha * gamma h) N := by
    have hev : ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ (Finset.univ : Finset H),
          engelsmaMaynardRadius (alpha * beta h) N ≤
            engelsmaMaynardRadius (alpha * gamma h) N := by
      apply (Finset.univ : Finset H).eventually_all.mpr
      intro h hh
      exact eventually_engelsmaMaynardRadius_mono_exponent
        (mul_le_mul_of_nonneg_left (horder h) halpha.le)
    filter_upwards [hev] with N hN h
    exact hN h (Finset.mem_univ h)
  filter_upwards [horderEvent] with N hQ
  unfold normalizedEngelsmaFractionalTupleShellMass
    engelsmaFractionalTupleShellMass engelsmaFractionalTupleShell
  rw [reciprocalTotientTupleWeight_sum_squarefreeCoprimeTupleShell_eq hQ]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Fintype.card_coe]
  rw [Finset.card_univ]
  simp only [Fintype.card_coe]

theorem tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
    {ι : Type*} {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (I : Finset ι) (coeff : ι → ℝ)
    (beta gamma : ι → H → ℝ)
    (hbeta : ∀ i ∈ I, ∀ h, beta i h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ i ∈ I, ∀ h, gamma i h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ i ∈ I, ∀ h, beta i h ≤ gamma i h) :
    Tendsto (fun N : ℕ =>
      ∑ i ∈ I, coeff i *
        normalizedEngelsmaFractionalTupleShellMass H alpha
          (beta i) (gamma i) N)
      atTop (nhds (∑ i ∈ I, coeff i *
        ∏ h : H, (gamma i h - beta i h))) := by
  apply tendsto_finsetSum I
  intro i hi
  have hlim := tendsto_normalizedEngelsmaFractionalTupleShellMass
    halpha (beta i) (gamma i)
    (hbeta i hi) (hgamma i hi) (horder i hi)
  exact hlim.const_mul (coeff i)

end BoundedGaps.Maynard
