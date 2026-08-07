import BoundedGaps.Maynard.ConcreteS2ReciprocalGMeanLimit
import BoundedGaps.Maynard.ConcreteScalarEndpointZero
import BoundedGaps.Maynard.ConcreteFractionalRectangle

noncomputable section

/-! Product-shell limits for the reciprocal-g short-endpoint measure. -/

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

theorem maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_squarefree
    {W n : ℕ} (hn : ¬Squarefree n) :
    maynardS2ReciprocalGSquarefreeAF W n = 0 := by
  unfold maynardS2ReciprocalGSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn
  simp [hmu]

theorem maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_coprime
    {W n : ℕ} (hcop : ¬Nat.Coprime n W) :
    maynardS2ReciprocalGSquarefreeAF W n = 0 := by
  by_cases hn : n = 0
  · subst n
    exact (maynardS2ReciprocalGSquarefreeAF W).map_zero
  obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpMem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn
  unfold maynardS2ReciprocalGSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  rw [maynardS2ReciprocalGWeightAF,
    ArithmeticFunction.prodPrimeFactors_apply hn]
  have hprod : ∏ q ∈ n.primeFactors,
      (if q ∣ W then 0 else (1 : ℝ) / ((q - 2 : ℕ) : ℝ)) = 0 := by
    apply Finset.prod_eq_zero hpMem
    simp [hpW]
  rw [show (∏ x ∈ n.primeFactors,
      (if x ∣ W then 0 else (1 : ℝ) / ((x - 2 : ℕ) : ℝ))) = 0 from hprod]
  simp

theorem maynardS2ReciprocalGSquarefreeAF_nonneg (W n : ℕ) :
    0 ≤ maynardS2ReciprocalGSquarefreeAF W n := by
  by_cases hn : Squarefree n
  · by_cases hcop : Nat.Coprime n W
    · rw [maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime hn hcop]
      positivity
    · rw [maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_coprime hcop]
  · rw [maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_squarefree hn]

theorem maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean
    (W Q : ℕ) :
    (∑ n ∈ squarefreeCoprimeCoordinateSupport W Q,
      maynardS2ReciprocalGSquarefreeAF W n) =
      maynardS2ReciprocalGSquarefreeMean W Q := by
  unfold maynardS2ReciprocalGSquarefreeMean
  apply Finset.sum_subset
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hnFull hnNot
    by_cases hsq : Squarefree n
    · by_cases hcop : Nat.Coprime n W
      · exact False.elim (hnNot (Finset.mem_filter.mpr ⟨hnFull, hsq, hcop⟩))
      · rw [maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_coprime hcop]
    · rw [maynardS2ReciprocalGSquarefreeAF_eq_zero_of_not_squarefree hsq]

theorem maynardS2ReciprocalGSquarefreeCoordinateShell_sum_eq_sub_mean
    {W Qlo Qhi : ℕ} (hQ : Qlo ≤ Qhi) :
    (∑ n ∈ squarefreeCoprimeCoordinateShell W Qlo Qhi,
      maynardS2ReciprocalGSquarefreeAF W n) =
      maynardS2ReciprocalGSquarefreeMean W Qhi -
        maynardS2ReciprocalGSquarefreeMean W Qlo := by
  unfold squarefreeCoprimeCoordinateShell
  rw [← maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean W Qhi,
    ← maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean W Qlo]
  rw [Finset.sum_sdiff_eq_sub]
  exact squarefreeCoprimeCoordinateSupport_subset hQ

theorem maynardS2ReciprocalGSquarefreeMean_one (W : ℕ) :
    maynardS2ReciprocalGSquarefreeMean W 1 = 1 := by
  unfold maynardS2ReciprocalGSquarefreeMean
  rw [show Finset.Icc 1 1 = {1} by ext n; simp]
  simp only [Finset.sum_singleton]
  exact (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).map_one

theorem tendsto_engelsmaS2ReciprocalGSquarefreeMean_fractionalRadius_nonneg
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 ≤ beta) :
    Tendsto (fun N : ℕ =>
      maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds beta) := by
  by_cases hzero : beta = 0
  · subst beta
    have hInv := tendsto_inv_engelsmaSingularSeries_mul_logRadius_zero halpha
    apply hInv.congr'
    filter_upwards [] with N
    have hR : engelsmaMaynardRadius (0 : ℝ) N = 1 := by
      unfold engelsmaMaynardRadius maynardDivisorCutoff
      simp
    simp [mul_zero, hR, maynardS2ReciprocalGSquarefreeMean_one]
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
    have hgamma : 0 < alpha * beta := mul_pos halpha hbetaPos
    have hmean :=
      tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one hgamma
    have hratio := tendsto_log_engelsmaMaynardRadius_ratio hgamma halpha
    have hproduct : Tendsto (fun N : ℕ =>
        (maynardS2ReciprocalGSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta) N) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius (alpha * beta) N))) *
        (Real.log (engelsmaMaynardRadius (alpha * beta) N) /
          Real.log (engelsmaMaynardRadius alpha N)))
        atTop (nhds beta) := by
      simpa [ne_of_gt halpha] using hmean.mul hratio
    apply hproduct.congr'
    filter_upwards [
      (tendsto_log_engelsmaMaynardRadius_atTop hgamma).eventually
        (eventually_ne_atTop 0),
      (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
        (eventually_ne_atTop 0)] with N hGamma hAlpha
    have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
    field_simp [hS.ne', hGamma, hAlpha]

def maynardS2ReciprocalGTupleShell
    (H : Finset ℕ) (W : ℕ) (Qlo Qhi : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun h =>
    squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h)

def maynardS2ReciprocalGTupleShellMass
    (H : Finset ℕ) (W : ℕ) (Qlo Qhi : H → ℕ) : ℝ :=
  ∑ u ∈ maynardS2ReciprocalGTupleShell H W Qlo Qhi,
    ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)

theorem maynardS2ReciprocalGTupleShellMass_eq_prod_sub_mean
    {H : Finset ℕ} {W : ℕ} {Qlo Qhi : H → ℕ}
    (hQ : ∀ h : H, Qlo h ≤ Qhi h) :
    maynardS2ReciprocalGTupleShellMass H W Qlo Qhi =
      ∏ h : H,
        (maynardS2ReciprocalGSquarefreeMean W (Qhi h) -
          maynardS2ReciprocalGSquarefreeMean W (Qlo h)) := by
  unfold maynardS2ReciprocalGTupleShellMass maynardS2ReciprocalGTupleShell
  calc
    (∑ u ∈ Fintype.piFinset
        (fun h : H => squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h)),
        ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)) =
        ∏ h : H, ∑ n ∈ squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h),
          maynardS2ReciprocalGSquarefreeAF W n := by
      exact (Finset.prod_univ_sum
        (fun h : H => squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h))
        (fun h : H => fun n => maynardS2ReciprocalGSquarefreeAF W n)).symm
    _ = ∏ h : H,
        (maynardS2ReciprocalGSquarefreeMean W (Qhi h) -
          maynardS2ReciprocalGSquarefreeMean W (Qlo h)) := by
      apply Finset.prod_congr rfl
      intro h hh
      exact maynardS2ReciprocalGSquarefreeCoordinateShell_sum_eq_sub_mean
        (hQ h)

def normalizedMaynardS2ReciprocalGTupleShellMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ)
    (Qlo Qhi : H → ℕ) : ℝ :=
  maynardS2ReciprocalGTupleShellMass H
      (engelsmaMaynardModulus N) Qlo Qhi /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

set_option maxRecDepth 6000 in
theorem tendsto_normalizedMaynardS2ReciprocalGTupleShellMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta gamma : H → ℝ)
    (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ h, gamma h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ h, beta h ≤ gamma h) :
    Tendsto (fun N : ℕ =>
      normalizedMaynardS2ReciprocalGTupleShellMass H alpha N
        (fun h => engelsmaMaynardRadius (alpha * beta h) N)
        (fun h => engelsmaMaynardRadius (alpha * gamma h) N))
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * gamma h) N) -
        maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (gamma h - beta h)) := by
    intro h
    have hgammaT :=
      tendsto_engelsmaS2ReciprocalGSquarefreeMean_fractionalRadius_nonneg
        halpha (hgamma h).1
    have hbetaT :=
      tendsto_engelsmaS2ReciprocalGSquarefreeMean_fractionalRadius_nonneg
        halpha (hbeta h).1
    have hdiff := hgammaT.sub hbetaT
    apply hdiff.congr'
    have hmul : alpha * beta h ≤ alpha * gamma h :=
      mul_le_mul_of_nonneg_left (horder h) halpha.le
    filter_upwards [eventually_engelsmaMaynardRadius_mono_exponent hmul] with
      N hQ
    rw [sub_div]
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        (maynardS2ReciprocalGSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * gamma h) N) -
          maynardS2ReciprocalGSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta h) N)) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
    apply tendsto_finsetProd Finset.univ
    intro h hh
    exact hcoord h
  apply hprod.congr'
  have horderEvent : ∀ᶠ N : ℕ in atTop, ∀ h : H,
      engelsmaMaynardRadius (alpha * beta h) N ≤
        engelsmaMaynardRadius (alpha * gamma h) N := by
    have hev : ∀ᶠ N : ℕ in atTop, ∀ h ∈ (Finset.univ : Finset H),
        engelsmaMaynardRadius (alpha * beta h) N ≤
          engelsmaMaynardRadius (alpha * gamma h) N := by
      apply (Finset.univ : Finset H).eventually_all.mpr
      intro h hh
      exact eventually_engelsmaMaynardRadius_mono_exponent
        (mul_le_mul_of_nonneg_left (horder h) halpha.le)
    filter_upwards [hev] with N hN h
    exact hN h (Finset.mem_univ h)
  filter_upwards [horderEvent] with N hN
  unfold normalizedMaynardS2ReciprocalGTupleShellMass
  rw [Finset.prod_div_distrib]
  rw [maynardS2ReciprocalGTupleShellMass_eq_prod_sub_mean]
  · simp only [Finset.prod_const, Fintype.card_coe]
    rw [Finset.card_univ]
    simp only [Fintype.card_coe]
  · intro h
    exact hN h

theorem tendsto_finite_linear_combination_normalizedMaynardS2ReciprocalGTupleShellMass
    {ι : Type*} {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (I : Finset ι) (coeff : ι → ℝ)
    (beta gamma : ι → H → ℝ)
    (hbeta : ∀ i ∈ I, ∀ h, beta i h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ i ∈ I, ∀ h, gamma i h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ i ∈ I, ∀ h, beta i h ≤ gamma i h) :
    Tendsto (fun N : ℕ =>
      ∑ i ∈ I, coeff i *
        normalizedMaynardS2ReciprocalGTupleShellMass H alpha N
          (fun h => engelsmaMaynardRadius (alpha * beta i h) N)
          (fun h => engelsmaMaynardRadius (alpha * gamma i h) N))
      atTop (nhds (∑ i ∈ I, coeff i *
        ∏ h : H, (gamma i h - beta i h))) := by
  apply tendsto_finsetSum I
  intro i hi
  have hlim := tendsto_normalizedMaynardS2ReciprocalGTupleShellMass
    halpha (beta i) (gamma i)
    (hbeta i hi) (hgamma i hi) (horder i hi)
  exact hlim.const_mul (coeff i)

end BoundedGaps.Maynard
