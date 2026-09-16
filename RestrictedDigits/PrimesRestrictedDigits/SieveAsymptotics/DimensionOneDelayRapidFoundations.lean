import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayWeightedShift

/-!
# Calculus for the explicit dimension-one rapid weight

This fixes an explicit specialization of Iwaniec's Lemma 16 weight and derives the corrected
logarithmic derivative numerator. See `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 191--193.
-/

open Set

namespace PrimesRestrictedDigits

/-- The logarithmic factor for the explicit choice
`epsilon = 1 / (128 * exp 1)`. -/
noncomputable def dimensionOneDelayLogWeight (s : Real) : Real :=
  Real.log (s / 128)

/-- The source weight `(epsilon * s)^s`, expressed with `exp` to keep its
calculus free of real-power side conditions. -/
noncomputable def dimensionOneDelayRapidWeight (s : Real) : Real :=
  Real.exp (s * (dimensionOneDelayLogWeight s - 1))

/-- On the positive domain, the exponential implementation is exactly the
real power `(epsilon * s)^s` used by Iwaniec, with
`epsilon = 1 / (128 * exp 1)`. -/
theorem dimensionOneDelayRapidWeight_eq_rpow
    {s : Real} (hs : 0 < s) :
    dimensionOneDelayRapidWeight s =
      (s / (128 * Real.exp 1)) ^ s := by
  have hExp : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hDen : (128 : Real) * Real.exp 1 ≠ 0 :=
    mul_ne_zero (by norm_num) hExp
  have hBase : 0 < s / (128 * Real.exp 1) :=
    div_pos hs (mul_pos (by norm_num) (Real.exp_pos 1))
  rw [Real.rpow_def_of_pos hBase]
  unfold dimensionOneDelayRapidWeight dimensionOneDelayLogWeight
  congr 1
  rw [Real.log_div hs.ne' hDen,
    Real.log_div hs.ne' (by norm_num : (128 : Real) ≠ 0),
    Real.log_mul (by norm_num : (128 : Real) ≠ 0) hExp,
    Real.log_exp]
  ring

/-- The quantity made decreasing in the explicit repair of Lemma 16. -/
noncomputable def dimensionOneDelayRapidWeightedSum (s : Real) : Real :=
  dimensionOneDelayRapidWeight s *
    (s ^ 2 * dimensionOneDelaySum s)

/-- The sign-controlling numerator in the derivative of the rapid weighted
sum. -/
noncomputable def dimensionOneDelayRapidDefect (s : Real) : Real :=
  s * dimensionOneDelaySum s * dimensionOneDelayLogWeight s -
    dimensionOneDelaySum (s - 1)

theorem dimensionOneDelayLogWeight_continuousOn :
    ContinuousOn dimensionOneDelayLogWeight (Ioi 0) := by
  unfold dimensionOneDelayLogWeight
  exact (continuous_id.div_const 128).continuousOn.log fun s hs =>
    div_ne_zero hs.ne' (by norm_num)

theorem dimensionOneDelayRapidWeight_continuousOn :
    ContinuousOn dimensionOneDelayRapidWeight (Ioi 0) := by
  unfold dimensionOneDelayRapidWeight
  exact Real.continuous_exp.comp_continuousOn
    (continuousOn_id.mul
      (dimensionOneDelayLogWeight_continuousOn.sub continuousOn_const))

theorem dimensionOneDelayRapidWeightedSum_continuousOn :
    ContinuousOn dimensionOneDelayRapidWeightedSum (Ioi 0) := by
  unfold dimensionOneDelayRapidWeightedSum
  exact dimensionOneDelayRapidWeight_continuousOn.mul
    ((continuousOn_id.pow 2).mul dimensionOneDelaySum_continuousOn)

theorem dimensionOneDelayRapidDefect_continuousOn :
    ContinuousOn dimensionOneDelayRapidDefect (Ioi 1) := by
  have hSum : ContinuousOn dimensionOneDelaySum (Ioi (1 : Real)) :=
    dimensionOneDelaySum_continuousOn.mono fun s hs => by
      change 1 < s at hs
      change 0 < s
      linarith
  have hLog : ContinuousOn dimensionOneDelayLogWeight (Ioi (1 : Real)) :=
    dimensionOneDelayLogWeight_continuousOn.mono fun s hs => by
      change 1 < s at hs
      change 0 < s
      linarith
  have hShift : ContinuousOn
      (fun s : Real => dimensionOneDelaySum (s - 1)) (Ioi 1) :=
    dimensionOneDelaySum_continuousOn.comp
      (continuous_id.sub continuous_const).continuousOn fun s hs => by
        change 1 < s at hs
        change 0 < s - 1
        linarith
  exact ((continuousOn_id.mul hSum).mul hLog).sub hShift

theorem dimensionOneDelayLogWeight_hasDerivAt
    {s : Real} (hs : 0 < s) :
    HasDerivAt dimensionOneDelayLogWeight (1 / s) s := by
  unfold dimensionOneDelayLogWeight
  have h := (Real.hasDerivAt_log
    (div_ne_zero hs.ne' (by norm_num : (128 : Real) ≠ 0))).comp s
      ((hasDerivAt_id s).div_const 128)
  simp only [id_eq] at h
  apply h.congr_deriv
  field_simp

theorem dimensionOneDelayRapidWeight_hasDerivAt
    {s : Real} (hs : 0 < s) :
    HasDerivAt dimensionOneDelayRapidWeight
      (dimensionOneDelayRapidWeight s *
        dimensionOneDelayLogWeight s) s := by
  have hExponentRaw := (hasDerivAt_id s).mul
    ((dimensionOneDelayLogWeight_hasDerivAt hs).sub_const 1)
  simp only [id_eq, one_mul] at hExponentRaw
  have hExponent : HasDerivAt
      (fun t : Real => t * (dimensionOneDelayLogWeight t - 1))
      (dimensionOneDelayLogWeight s) s := by
    apply hExponentRaw.congr_deriv
    field_simp
    ring
  unfold dimensionOneDelayRapidWeight
  exact (Real.hasDerivAt_exp
    (s * (dimensionOneDelayLogWeight s - 1))).comp s hExponent

theorem sq_mul_dimensionOneDelaySum_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt (fun t : Real => t ^ 2 * dimensionOneDelaySum t)
      (-s * dimensionOneDelaySum (s - 1)) s := by
  have h := (hasDerivAt_pow 2 s).mul
    (dimensionOneDelaySum_hasDerivAt hs)
  apply h.congr_deriv
  field_simp
  ring

theorem dimensionOneDelayRapidWeightedSum_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelayRapidWeightedSum
      (dimensionOneDelayRapidWeight s * s *
        dimensionOneDelayRapidDefect s) s := by
  unfold dimensionOneDelayRapidWeightedSum
  have h :=
    (dimensionOneDelayRapidWeight_hasDerivAt (by linarith)).mul
      (sq_mul_dimensionOneDelaySum_hasDerivAt hs)
  apply h.congr_deriv
  unfold dimensionOneDelayRapidDefect
  ring

end PrimesRestrictedDigits
