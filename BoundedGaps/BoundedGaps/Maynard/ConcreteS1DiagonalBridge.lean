import BoundedGaps.Maynard.ConcreteS1Diagonal
import BoundedGaps.Maynard.ConcreteS1CrossLimit
import BoundedGaps.Maynard.ConcreteS1Asymptotics

namespace BoundedGaps.Maynard

open Filter

/-! The exact diagonal/cross split transfers a diagonal limit to S1. -/

theorem tendsto_engelsmaMaynardS1Main_of_diagonal_limit
    {alpha I : ℝ} (halpha : 0 < alpha)
    (hdiag : Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds I)) :
    Tendsto
      (fun N : ℕ => engelsmaMaynardS1Main alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds I) := by
  have hcross := tendsto_normalized_engelsmaMaynardS1CrossCorrection_zero halpha
  have hdiff : Tendsto
      (fun N : ℕ =>
        engelsmaMaynardS1Main alpha N /
            engelsmaMaynardScale alpha N -
          ((N : ℝ) / engelsmaMaynardModulus N *
            engelsmaMaynardYDiagonal alpha N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
    have hneg : Tendsto (fun N : ℕ =>
        -(((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardS1CrossCorrection alpha N) /
            engelsmaMaynardScale alpha N)) atTop (nhds 0) := by
      simpa using hcross.neg
    apply hneg.congr'
    filter_upwards [] with N
    rw [engelsmaMaynardS1Main_eq_diagonal_sub_cross]
    ring
  have hsum := hdiag.add hdiff
  have hsum' : Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardYDiagonal alpha N) /
            engelsmaMaynardScale alpha N +
          (engelsmaMaynardS1Main alpha N /
            engelsmaMaynardScale alpha N -
            ((N : ℝ) / engelsmaMaynardModulus N *
              engelsmaMaynardYDiagonal alpha N) /
              engelsmaMaynardScale alpha N))
      atTop (nhds I) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [] with N
  ring

theorem tendsto_engelsmaMaynardS1_of_diagonal_limit_and_error
    {alpha I : ℝ} (halpha : 0 < alpha)
    (hdiag : Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds I))
    (herror : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds I) := by
  exact tendsto_engelsmaMaynardS1_of_main_error halpha
    (tendsto_engelsmaMaynardS1Main_of_diagonal_limit halpha hdiag) herror

theorem tendsto_engelsmaMaynardS1_of_diagonal_limit
    {alpha I : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (hdiag : Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds I)) :
    Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds I) := by
  apply tendsto_engelsmaMaynardS1_of_diagonal_limit_and_error halpha hdiag
  exact tendsto_engelsmaMaynardS1Error_zero_of_explicit_log_envelope halpha
    (tendsto_engelsmaMaynardS1ExplicitEnvelope halpha halphaQuarter)

end BoundedGaps.Maynard
