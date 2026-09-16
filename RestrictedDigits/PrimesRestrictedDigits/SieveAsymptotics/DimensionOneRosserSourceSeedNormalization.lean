import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeed
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialFactor

/-!
# Conditional source-cutoff normalization of the high-rank seed

This proves the elementary scalar implication from a pointwise lower
Eq. (6.5)-scale delay bound to the normalized seed used in Iwaniec's Eq. (8.13).
-/

open Set

namespace PrimesRestrictedDigits

/-- The explicit lower scale corresponding to the lower half of the
dimension-one Eq. (6.5) asymptotic. -/
noncomputable def dimensionOneDelayLowerScale (C s : Real) : Real :=
  Real.exp (-s * Real.log s - s * Real.log (Real.log s) + s -
    C * s * Real.log (Real.log (2 * s)) / Real.log s)

private theorem sourceCutoff_log_data
    {L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3) :
    0 < s /\ 0 < L /\ 0 < Real.log s /\ 1 <= Real.log L /\
      50 * Real.log s = Real.log L + 3 * Real.log (Real.log L) /\
      Real.log L <= 50 * Real.log s /\
      Real.log (Real.log L) <= Real.log s /\
      47 * Real.log s <= Real.log L := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hellLarge : 5000 < Real.log s :=
    dimensionOneRosserSeed_log_gt hsLarge
  have hell : 0 < Real.log s := by linarith
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hu : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have huPos : 0 < Real.log L := zero_lt_one.trans_le hu
  have hlogEq := congrArg Real.log hcutoff
  rw [Real.log_pow, Real.log_mul hLPos.ne'
      (pow_ne_zero 3 huPos.ne'), Real.log_pow] at hlogEq
  norm_num at hlogEq
  have huLogNonneg : 0 <= Real.log (Real.log L) := Real.log_nonneg hu
  have huLe : Real.log L <= 50 * Real.log s := by linarith
  have hSeed := dimensionOneRosserSeed_log_mul_lt hsLarge
  have huLtS : Real.log L < s := by linarith
  have hlogu : Real.log (Real.log L) <= Real.log s :=
    Real.log_le_log huPos huLtS.le
  have h47 : 47 * Real.log s <= Real.log L := by linarith
  exact ⟨hs, hLPos, hell, hu, hlogEq, huLe, hlogu, h47⟩

private theorem sourceArtificial_log_lower
    {L s : Real} (hLPos : 0 < L) (hell : 0 < Real.log s)
    (hu : 1 <= Real.log L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
    (h47 : 47 * Real.log s <= Real.log L) :
    3 * (Real.log (Real.log s) + Real.log 47) <=
      Real.log (dimensionOneRosserArtificialBase L 0 s) := by
  have huPos : 0 < Real.log L := zero_lt_one.trans_le hu
  have hprodPos : 0 < 47 * Real.log s := mul_pos (by norm_num) hell
  have hpow : (47 * Real.log s) ^ 3 <= (Real.log L) ^ 3 :=
    pow_le_pow_left₀ hprodPos.le h47 3
  have huPow : 0 <= (Real.log L) ^ 3 := (pow_pos huPos 3).le
  have hpow' : (47 * Real.log s) ^ 3 <= 1 + (Real.log L) ^ 3 := by
    linarith
  have hlog := Real.log_le_log (pow_pos hprodPos 3) hpow'
  have hleft : Real.log ((47 * Real.log s) ^ 3) =
      3 * (Real.log (Real.log s) + Real.log 47) := by
    rw [Real.log_pow, Real.log_mul (by norm_num : (47 : Real) ≠ 0) hell.ne']
    ring
  have hratio : s ^ 50 / L = (Real.log L) ^ 3 := by
    rw [div_eq_iff hLPos.ne']
    simpa only [mul_comm] using hcutoff
  calc
    3 * (Real.log (Real.log s) + Real.log 47) =
        Real.log ((47 * Real.log s) ^ 3) := hleft.symm
    _ <= Real.log (1 + (Real.log L) ^ 3) := hlog
    _ = Real.log (dimensionOneRosserArtificialBase L 0 s) := by
      rw [dimensionOneRosserArtificialBase, add_zero, hratio]

private theorem sourceConstant_reserve
    {s : Real} (hellLarge : 5000 < Real.log s) :
    8 + Real.log 1024 <
      Real.log (Real.log s) + 3 * Real.log 47 := by
  have hellPos : 0 < Real.log s := by linarith
  have hlogEll : 12 * Real.log 2 < Real.log (Real.log s) := by
    have h := Real.strictMonoOn_log
      (show (4096 : Real) ∈ Ioi 0 by norm_num)
      (show Real.log s ∈ Ioi 0 by exact hellPos)
      (by linarith)
    rw [show (4096 : Real) = 2 ^ 12 by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  have hlog47 : 5 * Real.log 2 < Real.log 47 := by
    have h := Real.strictMonoOn_log
      (show (32 : Real) ∈ Ioi 0 by norm_num)
      (show (47 : Real) ∈ Ioi 0 by norm_num)
      (by norm_num)
    rw [show (32 : Real) = 2 ^ 5 by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  have hlog1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : Real) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hlog1024]
  linarith [Real.log_two_gt_d9]

private theorem sourceNormalization_cost
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

private theorem sourceLog_budget
    {C L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s) :
    2 * s * Real.log (Real.log s) +
          (3 + Real.log 1024) * s +
          C * s * Real.log (Real.log (2 * s)) / Real.log s +
          (3 / 8 : Real) * Real.log L + Real.log 4 <
      s * Real.log (dimensionOneRosserArtificialBase L 0 s) +
        2 * Real.log s := by
  obtain ⟨hs, hLPos, hell, hu, _hlogEq, huLe, _hlogu, h47⟩ :=
    sourceCutoff_log_data hsLarge hL hcutoff
  have hellLarge := dimensionOneRosserSeed_log_gt hsLarge
  have hfactor := sourceArtificial_log_lower hLPos hell hu hcutoff h47
  have hconstant := sourceConstant_reserve hellLarge
  have hnormal := sourceNormalization_cost hsLarge huLe
  have herrorScaled :
      C * s * Real.log (Real.log (2 * s)) / Real.log s <= s := by
    rw [div_le_iff₀ hell]
    have hmul := mul_le_mul_of_nonneg_left herror hs.le
    nlinarith
  have hfactorScaled := mul_le_mul_of_nonneg_left hfactor hs.le
  have hconstantScaled := mul_lt_mul_of_pos_left hconstant hs
  nlinarith

private theorem sourceNormalizedCandidate_log
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

private theorem seedEnvelope_lt_sourceCandidate
    {C L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
    (herror : C * Real.log (Real.log (2 * s)) <= Real.log s) :
    dimensionOneRosserSeedEnvelope s <
      dimensionOneRosserArtificialFactor L 0 s *
        (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
        L ^ (-3 / 8 : Real) := by
  obtain ⟨hs, hLPos, hell, _hu, _hlogEq, _huLe, _hlogu, _h47⟩ :=
    sourceCutoff_log_data hsLarge hL hcutoff
  have hA : 0 < dimensionOneRosserArtificialFactor L 0 s := Real.exp_pos _
  have hquarter : 0 < s ^ 2 / 4 := div_pos (sq_pos_of_pos hs) (by norm_num)
  have hE : 0 < dimensionOneDelayLowerScale C s := Real.exp_pos _
  have hpow : 0 < L ^ (-3 / 8 : Real) := Real.rpow_pos_of_pos hLPos _
  have hproduct : 0 <
      dimensionOneRosserArtificialFactor L 0 s *
        (s ^ 2 / 4 * dimensionOneDelayLowerScale C s) *
        L ^ (-3 / 8 : Real) :=
    mul_pos (mul_pos hA (mul_pos hquarter hE)) hpow
  have hbudget := sourceLog_budget hsLarge hL hcutoff herror
  have hlogProduct := sourceNormalizedCandidate_log (C := C) hs hLPos
  have hlogTilt :
      Real.log (dimensionOneRosserSeedTilt s) =
        Real.log s - Real.log 1024 - Real.log (Real.log s) := by
    have hden : 0 < 1024 * Real.log s := mul_pos (by norm_num) hell
    rw [dimensionOneRosserSeedTilt, Real.log_div hs.ne' hden.ne',
      Real.log_mul (by norm_num : (1024 : Real) ≠ 0) hell.ne']
    ring
  unfold dimensionOneRosserSeedEnvelope
  apply (Real.lt_log_iff_exp_lt hproduct).1
  rw [hlogProduct, hlogTilt]
  nlinarith

private theorem seedEnvelope_lt_sourceNormalized_of_quarter
    {C L s Q : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
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
      seedEnvelope_lt_sourceCandidate hsLarge hL hcutoff herror
    _ < dimensionOneRosserArtificialFactor L 0 s *
          (s ^ 2 * Q) * L ^ (-3 / 8 : Real) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hscaled hA) hpow

/-- A pointwise lower delay estimate normalizes the independent upper seed at
the exact source cutoff. -/
theorem dimensionOneRosserSeedEnvelope_lt_sourceNormalizedPlus
    {C L s : Real} (_hC : 0 <= C)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
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
  have h := seedEnvelope_lt_sourceNormalized_of_quarter hsLarge hL hcutoff
    herror hquarter
  rwa [sq_mul_dimensionOneDelayQPlus hs.ne'] at h

/-- A pointwise lower delay estimate normalizes the independent lower seed at
the exact source cutoff. -/
theorem dimensionOneRosserSeedEnvelope_lt_sourceNormalizedMinus
    {C L s : Real} (_hC : 0 <= C)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= L)
    (hcutoff : s ^ 50 = L * (Real.log L) ^ 3)
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
  have h := seedEnvelope_lt_sourceNormalized_of_quarter hsLarge hL hcutoff
    herror hquarter
  rwa [sq_mul_dimensionOneDelayQMinus hs.ne'] at h

end PrimesRestrictedDigits
