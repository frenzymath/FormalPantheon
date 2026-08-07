import BoundedGaps.Maynard.ConcreteScalarEndpointUniform
import BoundedGaps.Maynard.MaynardYDiagonalCollisionBox

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def squarefreeCoprimeCoordinateSupport (W Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter fun n => Squarefree n ∧ Nat.Coprime n W

def squarefreeCoprimeTupleBox
    (H : Finset ℕ) (W : ℕ) (Q : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun h => squarefreeCoprimeCoordinateSupport W (Q h)

theorem squarefreeCoprimeCoordinateSupport_sum (W Q : ℕ) :
    (∑ n ∈ squarefreeCoprimeCoordinateSupport W Q,
      (1 : ℝ) / Nat.totient n) =
      squarefreeCoprimeInvTotientMean W Q := by
  unfold squarefreeCoprimeCoordinateSupport squarefreeCoprimeInvTotientMean
  simp only [Finset.sum_filter]

theorem reciprocalTotientTupleWeight_sum_squarefreeCoprimeTupleBox_eq
    {H : Finset ℕ} {W : ℕ} {Q : H → ℕ} :
    (∑ u ∈ squarefreeCoprimeTupleBox H W Q,
      reciprocalTotientTupleWeight H u) =
      ∏ h : H, squarefreeCoprimeInvTotientMean W (Q h) := by
  rw [squarefreeCoprimeTupleBox,
    reciprocalTotientTupleWeight_sum_pi_eq_prod]
  apply Finset.prod_congr rfl
  intro h hh
  exact squarefreeCoprimeCoordinateSupport_sum W (Q h)

def engelsmaFractionalTupleBox
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : Finset (H → ℕ) :=
  squarefreeCoprimeTupleBox H (engelsmaMaynardModulus N)
    (fun h => engelsmaMaynardRadius (alpha * beta h) N)

def engelsmaFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaFractionalTupleBox H alpha beta N,
    reciprocalTotientTupleWeight H u

def normalizedEngelsmaFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  engelsmaFractionalTupleBoxMass H alpha beta N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

theorem tendsto_engelsmaSquarefreeMean_fractionalRadius_nonneg
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 ≤ beta) :
    Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds beta) := by
  by_cases hzero : beta = 0
  · subst beta
    simpa only [mul_zero] using
      tendsto_engelsmaSquarefreeMean_zeroEndpoint halpha
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
    exact tendsto_engelsmaSquarefreeMean_fractionalRadius halpha hbetaPos

set_option maxRecDepth 10000 in
theorem tendsto_normalizedEngelsmaFractionalTupleBoxMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta : H → ℝ) (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaFractionalTupleBoxMass H alpha beta N)
      atTop (nhds (∏ h : H, beta h)) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (beta h)) := by
    intro h
    exact tendsto_engelsmaSquarefreeMean_fractionalRadius_nonneg halpha
      (hbeta h).1
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        squarefreeCoprimeInvTotientMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta h) N) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (∏ h : H, beta h)) := by
    apply tendsto_finsetProd Finset.univ
    intro h hh
    exact hcoord h
  apply hprod.congr'
  filter_upwards [] with N
  unfold normalizedEngelsmaFractionalTupleBoxMass
    engelsmaFractionalTupleBoxMass engelsmaFractionalTupleBox
  rw [reciprocalTotientTupleWeight_sum_squarefreeCoprimeTupleBox_eq]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Fintype.card_coe]
  rw [Finset.card_univ]
  simp only [Fintype.card_coe]

end BoundedGaps.Maynard
