import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceNormalizedScalar

/-!
# Direct source normalization above the selected cutoff

This generalizes the source-normalized high-seed scalar from cutoff equality to the weak
domain `L * (log L)^3 <= s^50`.
-/

namespace PrimesRestrictedDigits

private theorem sourceDirect_log_data
    {L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50) :
    0 < s /\ 0 < L /\ 0 < Real.log s /\ 1 <= Real.log L /\
      Real.log L + 3 * Real.log (Real.log L) <= 50 * Real.log s /\
      Real.log L <= 50 * Real.log s := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hell : 0 < Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hu : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have huPos : 0 < Real.log L := zero_lt_one.trans_le hu
  have hleftPos : 0 < L * (Real.log L) ^ 3 :=
    mul_pos hLPos (pow_pos huPos 3)
  have hrightPos : 0 < s ^ 50 := pow_pos hs 50
  have hlog := Real.log_le_log hleftPos hdom
  rw [Real.log_mul hLPos.ne' (pow_ne_zero 3 huPos.ne'),
    Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have huLogNonneg : 0 <= Real.log (Real.log L) := Real.log_nonneg hu
  refine ⟨hs, hLPos, hell, hu, hlog, ?_⟩
  linarith

private theorem sourceDirect_artificial_log_lower_near
    {L s : Real} (hLPos : 0 < L) (hell : 0 < Real.log s)
    (hu : 1 <= Real.log L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (h47 : 47 * Real.log s <= Real.log L) :
    3 * (Real.log (Real.log s) + Real.log 47) <=
      Real.log (dimensionOneRosserArtificialBase L 0 s) := by
  have huPos : 0 < Real.log L := zero_lt_one.trans_le hu
  have hprodPos : 0 < 47 * Real.log s := mul_pos (by norm_num) hell
  have hpow : (47 * Real.log s) ^ 3 <= (Real.log L) ^ 3 :=
    pow_le_pow_left₀ hprodPos.le h47 3
  have hratio : (Real.log L) ^ 3 <= s ^ 50 / L := by
    rw [le_div_iff₀ hLPos]
    nlinarith
  have hpow' : (47 * Real.log s) ^ 3 <= 1 + s ^ 50 / L := by
    linarith
  have hlog := Real.log_le_log (pow_pos hprodPos 3) hpow'
  have hleft : Real.log ((47 * Real.log s) ^ 3) =
      3 * (Real.log (Real.log s) + Real.log 47) := by
    rw [Real.log_pow, Real.log_mul (by norm_num : (47 : Real) ≠ 0)
      hell.ne']
    ring
  calc
    3 * (Real.log (Real.log s) + Real.log 47) =
        Real.log ((47 * Real.log s) ^ 3) := hleft.symm
    _ <= Real.log (1 + s ^ 50 / L) := hlog
    _ = Real.log (dimensionOneRosserArtificialBase L 0 s) := by
      simp [dimensionOneRosserArtificialBase]

private theorem sourceDirect_artificial_log_lower_far
    {L s : Real} (hs : 0 < s) (hLPos : 0 < L)
    (_hell : 0 < Real.log s)
    (hfar : Real.log L < 47 * Real.log s) :
    3 * Real.log s <
      Real.log (dimensionOneRosserArtificialBase L 0 s) := by
  have hpowPos : 0 < s ^ 50 := pow_pos hs 50
  have hratioPos : 0 < s ^ 50 / L := div_pos hpowPos hLPos
  have hbasePos : 0 < 1 + s ^ 50 / L := by positivity
  have hlogRatio : Real.log (s ^ 50 / L) =
      50 * Real.log s - Real.log L := by
    rw [Real.log_div (pow_ne_zero 50 hs.ne') hLPos.ne', Real.log_pow]
    norm_num
  have hthree : 3 * Real.log s < Real.log (s ^ 50 / L) := by
    rw [hlogRatio]
    linarith
  have hstrict : Real.log (s ^ 50 / L) <
      Real.log (1 + s ^ 50 / L) :=
    Real.strictMonoOn_log hratioPos hbasePos (by linarith)
  calc
    3 * Real.log s < Real.log (s ^ 50 / L) := hthree
    _ < Real.log (1 + s ^ 50 / L) := hstrict
    _ = Real.log (dimensionOneRosserArtificialBase L 0 s) := by
      simp [dimensionOneRosserArtificialBase]

private theorem sourceDirect_constant_reserve
    {s : Real} (hellLarge : 5000 < Real.log s) :
    8 + Real.log 1024 <
      Real.log (Real.log s) + 3 * Real.log 47 := by
  have hellPos : 0 < Real.log s := by linarith
  have hlogEll : 12 * Real.log 2 < Real.log (Real.log s) := by
    have h := Real.strictMonoOn_log
      (show (4096 : Real) ∈ Set.Ioi 0 by norm_num)
      (show Real.log s ∈ Set.Ioi 0 by exact hellPos) (by linarith)
    rw [show (4096 : Real) = 2 ^ 12 by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  have hlog47 : 5 * Real.log 2 < Real.log 47 := by
    have h := Real.strictMonoOn_log
      (show (32 : Real) ∈ Set.Ioi 0 by norm_num)
      (show (47 : Real) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rw [show (32 : Real) = 2 ^ 5 by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  have hlog1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : Real) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hlog1024]
  linarith [Real.log_two_gt_d9]

private theorem sourceDirect_normalization_cost
    {L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (huLe : Real.log L <= 50 * Real.log s) :
    (3 / 8 : Real) * Real.log L + Real.log 4 < 4 * s := by
  have hlogTwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : Real)) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hSeed := dimensionOneRosserSeed_log_mul_lt hsLarge
  have hellLarge := dimensionOneRosserSeed_log_gt hsLarge
  rw [hlogFour]
  linarith

private theorem sourceDirect_log_budget_ge
    {C L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s) :
    2 * s * Real.log (Real.log s) +
          (3 + Real.log 1024) * s +
          C * s * Real.log (Real.log (2 * s)) / Real.log s +
          (3 / 8 : Real) * Real.log L + Real.log 4 <
      s * Real.log (dimensionOneRosserArtificialBase L 0 s) +
        2 * Real.log s := by
  obtain ⟨hs, hLPos, hell, hu, _hlogDom, huLe⟩ :=
    sourceDirect_log_data hsLarge hL hdom
  have hellLarge := dimensionOneRosserSeed_log_gt hsLarge
  have herrorScaled :
      C * s * Real.log (Real.log (2 * s)) / Real.log s <= s := by
    rw [div_le_iff₀ hell]
    have hmul := mul_le_mul_of_nonneg_left herror hs.le
    nlinarith
  by_cases hnear : 47 * Real.log s <= Real.log L
  · have hfactor := sourceDirect_artificial_log_lower_near hLPos hell hu
      hdom hnear
    have hconstant := sourceDirect_constant_reserve hellLarge
    have hnormal := sourceDirect_normalization_cost hsLarge huLe
    have hfactorScaled := mul_le_mul_of_nonneg_left hfactor hs.le
    have hconstantScaled := mul_lt_mul_of_pos_left hconstant hs
    nlinarith
  · have hfar : Real.log L < 47 * Real.log s := lt_of_not_ge hnear
    have hfactor := sourceDirect_artificial_log_lower_far hs hLPos hell hfar
    have hfactorScaled := mul_lt_mul_of_pos_left hfactor hs
    have hloglog : Real.log (Real.log s) <= Real.log s - 1 :=
      Real.log_le_sub_one_of_pos hell
    have hloglogScaled := mul_le_mul_of_nonneg_left hloglog
      (by positivity : 0 <= 2 * s)
    have hlogTwo : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (x := (2 : Real)) (by norm_num)
        (by norm_num)
      norm_num at h
      exact h
    have hlog1024 : Real.log 1024 < 10 := by
      rw [show (1024 : Real) = 2 ^ 10 by norm_num, Real.log_pow]
      norm_num
      linarith
    have hconstantScaled := mul_lt_mul_of_pos_right
      (add_lt_add_left hlog1024 3) hs
    have hLcost : (3 / 8 : Real) * Real.log L < s := by
      have hSeed := dimensionOneRosserSeed_log_mul_lt hsLarge
      nlinarith
    have hlogFour : Real.log 4 < 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith
    have hsTwo : (2 : Real) < s := by
      have hExp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith [Real.exp_pos (5000 : Real)]
    have hlogFourS : Real.log 4 < s := hlogFour.trans hsTwo
    have hlinear : 16 * s < s * Real.log s := by
      nlinarith
    nlinarith

private theorem sourceDirect_candidate_log
    {C L s : Real} (hs : 0 < s) (hLPos : 0 < L) :
    Real.log
        (dimensionOneRosserArtificialFactor L 0 s *
          (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
          L ^ (-3 / 8 : Real)) =
      s * Real.log (dimensionOneRosserArtificialBase L 0 s) +
        (2 * Real.log s - Real.log 4) +
        (-s * Real.log s - s * Real.log (Real.log s) + s -
          C * s * Real.log (Real.log (2 * s)) / Real.log s) +
        (-3 / 8 : Real) * Real.log L := by
  have hA : 0 < dimensionOneRosserArtificialFactor L 0 s := Real.exp_pos _
  have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hquarter : 0 < s ^ 2 / 4 := div_pos hsSq (by norm_num)
  have hE : 0 < dimensionOneDelayLowerScale C s := Real.exp_pos _
  have hpow : 0 < L ^ (-3 / 8 : Real) := Real.rpow_pos_of_pos hLPos _
  rw [Real.log_mul (mul_ne_zero hA.ne'
      (mul_ne_zero hquarter.ne' hE.ne')) hpow.ne',
    Real.log_mul hA.ne' (mul_ne_zero hquarter.ne' hE.ne'),
    Real.log_mul hquarter.ne' hE.ne',
    Real.log_div (pow_ne_zero 2 hs.ne') (by norm_num : (4 : Real) ≠ 0),
    Real.log_pow, Real.log_rpow hLPos,
    dimensionOneRosserArtificialFactor, Real.log_exp,
    dimensionOneDelayLowerScale, Real.log_exp]
  ring

private theorem sourceDirect_seedEnvelope_lt_candidate
    {C L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s) :
    dimensionOneRosserSeedEnvelope s <
      dimensionOneRosserArtificialFactor L 0 s *
        (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
          L ^ (-3 / 8 : Real) := by
  obtain ⟨hs, hLPos, hell, _hu, _hlogDom, _huLe⟩ :=
    sourceDirect_log_data hsLarge hL hdom
  have hA : 0 < dimensionOneRosserArtificialFactor L 0 s := Real.exp_pos _
  have hquarter : 0 < s ^ 2 / 4 :=
    div_pos (sq_pos_of_pos hs) (by norm_num)
  have hE : 0 < dimensionOneDelayLowerScale C s := Real.exp_pos _
  have hpow : 0 < L ^ (-3 / 8 : Real) := Real.rpow_pos_of_pos hLPos _
  have hproduct : 0 <
      dimensionOneRosserArtificialFactor L 0 s *
        (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
          L ^ (-3 / 8 : Real) :=
    mul_pos (mul_pos hA (mul_pos hquarter hE)) hpow
  have hbudget := sourceDirect_log_budget_ge hsLarge hL hdom herror
  have hlogProduct := sourceDirect_candidate_log (C := C) hs hLPos
  have hlogTilt : Real.log (dimensionOneRosserSeedTilt s) =
      Real.log s - Real.log 1024 - Real.log (Real.log s) := by
    have hden : 0 < 1024 * Real.log s := mul_pos (by norm_num) hell
    rw [dimensionOneRosserSeedTilt, Real.log_div hs.ne' hden.ne',
      Real.log_mul (by norm_num : (1024 : Real) ≠ 0) hell.ne']
    ring
  unfold dimensionOneRosserSeedEnvelope
  apply (Real.lt_log_iff_exp_lt hproduct).1
  rw [hlogProduct, hlogTilt]
  nlinarith

private theorem sourceDirect_seedEnvelope_lt_normalized
    {C L s Q : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s)
    (hquarter : dimensionOneDelayLowerScale C s / 4 < Q) :
    dimensionOneRosserSeedEnvelope s <
      dimensionOneRosserArtificialFactor L 0 s *
        (s ^ 2 * Q) * L ^ (-3 / 8 : Real) := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hA : 0 < dimensionOneRosserArtificialFactor L 0 s := Real.exp_pos _
  have hpow : 0 < L ^ (-3 / 8 : Real) := Real.rpow_pos_of_pos hLPos _
  have hscaled :
      s ^ 2 / 4 * dimensionOneDelayLowerScale C s < s ^ 2 * Q := by
    have h := mul_lt_mul_of_pos_left hquarter (sq_pos_of_pos hs)
    nlinarith
  calc
    dimensionOneRosserSeedEnvelope s <
        dimensionOneRosserArtificialFactor L 0 s *
          (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
            L ^ (-3 / 8 : Real) :=
      sourceDirect_seedEnvelope_lt_candidate hsLarge hL hdom herror
    _ < dimensionOneRosserArtificialFactor L 0 s *
          (s ^ 2 * Q) * L ^ (-3 / 8 : Real) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hscaled hA) hpow

private theorem sourceDirect_seedEnvelope_lt_normalizedPlus
    {C L s : Real} (_hC : 0 <= C)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s)
    (hlower : dimensionOneDelayLowerScale C s <= dimensionOneDelaySum s) :
    dimensionOneRosserSeedEnvelope s <
      dimensionOneRosserArtificialFactor L 0 s *
        dimensionOneDelayScaledPlus s * L ^ (-3 / 8 : Real) := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hquarter : dimensionOneDelayLowerScale C s / 4 <
      dimensionOneDelayQPlus s :=
    (div_le_div_of_nonneg_right hlower (by norm_num)).trans_lt
      (dimensionOneDelayQPlus_bounds hs).1
  have h := sourceDirect_seedEnvelope_lt_normalized hsLarge hL hdom
    herror hquarter
  rwa [sq_mul_dimensionOneDelayQPlus hs.ne'] at h

private theorem sourceDirect_seedEnvelope_lt_normalizedMinus
    {C L s : Real} (_hC : 0 <= C)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hdom : L * (Real.log L) ^ 3 <= s ^ 50)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s)
    (hlower : dimensionOneDelayLowerScale C s <= dimensionOneDelaySum s) :
    dimensionOneRosserSeedEnvelope s <
      dimensionOneRosserArtificialFactor L 0 s *
        dimensionOneDelayScaledMinus s * L ^ (-3 / 8 : Real) := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hquarter : dimensionOneDelayLowerScale C s / 4 <
      dimensionOneDelayQMinus s :=
    (div_le_div_of_nonneg_right hlower (by norm_num)).trans_lt
      (dimensionOneDelayQMinus_bounds hs).1
  have h := sourceDirect_seedEnvelope_lt_normalized hsLarge hL hdom
    herror hquarter
  rwa [sq_mul_dimensionOneDelayQMinus hs.ne'] at h

/-- A single threshold gives both source-normalized high-seed inequalities on
the weak current-coordinate domain. -/
theorem exists_dimensionOneRosserSeedEnvelope_sourceNormalized_ge
    : exists C S : Real, 0 < C /\ Real.exp 5000 + 1 <= S /\
      forall {L s : Real}, S <= s -> Real.exp 1 <= L ->
        L * (Real.log L) ^ 3 <= s ^ 50 ->
        dimensionOneRosserSeedEnvelope s <
            dimensionOneRosserArtificialFactor L 0 s *
              dimensionOneDelayScaledPlus s * L ^ (-3 / 8 : Real) /\
        dimensionOneRosserSeedEnvelope s <
            dimensionOneRosserArtificialFactor L 0 s *
              dimensionOneDelayScaledMinus s * L ^ (-3 / 8 : Real) := by
  obtain ⟨C, S1, hC, _hS1, hLower⟩ :=
    exists_dimensionOneDelaySum_lowerScale
  obtain ⟨S2, hS2, hError⟩ :=
    exists_dimensionOneDelayLowerScale_error_threshold hC
  let S : Real := max S1 (max (Real.exp 5000 + 1) S2)
  refine ⟨C, S, hC, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro L s hsTail hL hdom
    have hs1 : S1 <= s := (le_max_left _ _).trans hsTail
    have hs2 : S2 <= s :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hsTail)
    have hsLarge : Real.exp 5000 + 1 <= s :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hsTail)
    have hlower : dimensionOneDelayLowerScale C s <=
        dimensionOneDelaySum s := (hLower hs1).le
    have herror : C * Real.log (Real.log (2 * s)) <= Real.log s :=
      hError hs2
    exact ⟨
      sourceDirect_seedEnvelope_lt_normalizedPlus hC.le hsLarge hL hdom
        herror hlower,
      sourceDirect_seedEnvelope_lt_normalizedMinus hC.le hsLarge hL hdom
        herror hlower⟩

end PrimesRestrictedDigits
