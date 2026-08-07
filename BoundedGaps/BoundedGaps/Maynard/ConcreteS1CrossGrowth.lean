import BoundedGaps.Maynard.ConcreteS1CrossBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

/-!
# Growth conditions for the concrete S1 cross bound

The exact triple logarithm gives a sharper primorial estimate than the generic
subpower bound.  This is enough to compare the pre-sieve modulus with the
logarithm of the natural divisor cutoff.
-/

namespace BoundedGaps.Maynard

open Filter Set

theorem tripleLogCutoff_cast_le_tripleLog
    {M : ℕ}
    (hlll : 0 ≤ Real.log (Real.log (Real.log (M : ℝ)))) :
    (tripleLogCutoff M : ℝ) ≤
      Real.log (Real.log (Real.log (M : ℝ))) := by
  unfold tripleLogCutoff
  exact Nat.floor_le hlll

theorem four_pow_tripleLogCutoff_le_logLog_rpow
    {M : ℕ}
    (hllpos : 0 < Real.log (Real.log (M : ℝ)))
    (hlll : 0 ≤ Real.log (Real.log (Real.log (M : ℝ)))) :
    ((4 ^ tripleLogCutoff M : ℕ) : ℝ) ≤
      Real.rpow (Real.log (Real.log (M : ℝ))) (Real.log 4) := by
  have hD := tripleLogCutoff_cast_le_tripleLog hlll
  calc
    ((4 ^ tripleLogCutoff M : ℕ) : ℝ) =
        Real.rpow (4 : ℝ) (tripleLogCutoff M : ℝ) := by
      push_cast
      exact (Real.rpow_natCast (4 : ℝ) (tripleLogCutoff M)).symm
    _ ≤ Real.rpow (4 : ℝ)
        (Real.log (Real.log (Real.log (M : ℝ)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
    _ = Real.rpow (Real.log (Real.log (M : ℝ))) (Real.log 4) := by
      change (4 : ℝ) ^ Real.log (Real.log (Real.log (M : ℝ))) =
        Real.log (Real.log (M : ℝ)) ^ Real.log 4
      rw [Real.rpow_def_of_pos (by norm_num),
        Real.rpow_def_of_pos hllpos]
      congr 1
      ring

theorem primorial_tripleLogCutoff_le_logLog_rpow
    {M : ℕ}
    (hllpos : 0 < Real.log (Real.log (M : ℝ)))
    (hlll : 0 ≤ Real.log (Real.log (Real.log (M : ℝ)))) :
    (primorial (tripleLogCutoff M) : ℝ) ≤
      Real.rpow (Real.log (Real.log (M : ℝ))) (Real.log 4) := by
  have hp : (primorial (tripleLogCutoff M) : ℝ) ≤
      ((4 ^ tripleLogCutoff M : ℕ) : ℝ) := by
    exact_mod_cast primorial_le_four_pow (tripleLogCutoff M)
  exact hp.trans (four_pow_tripleLogCutoff_le_logLog_rpow hllpos hlll)

theorem eventually_primorial_tripleLogCutoff_le_sqrt_log :
    ∀ᶠ M : ℕ in atTop,
      (primorial (tripleLogCutoff M) : ℝ) ≤
        Real.rpow (Real.log (M : ℝ)) (1 / 2 : ℝ) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hll : Tendsto
      (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlll : Tendsto
      (fun M : ℕ => Real.log (Real.log (Real.log (M : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hll
  have hsharp : ∀ᶠ M : ℕ in atTop,
      (primorial (tripleLogCutoff M) : ℝ) ≤
        Real.rpow (Real.log (Real.log (M : ℝ))) (Real.log 4) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0),
      hlll.eventually (eventually_ge_atTop 0)] with M hllpos hlllNonneg
    exact primorial_tripleLogCutoff_le_logLog_rpow hllpos hlllNonneg
  have hlittle := isLittleO_log_rpow_rpow_atTop
    (Real.log 4) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hdomRaw := (hlittle.comp_tendsto hlog).eventuallyLE
  have hlogNonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ Real.log (M : ℝ) :=
    hlog.eventually (eventually_ge_atTop 0)
  have hllNonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ Real.log (Real.log (M : ℝ)) :=
    hll.eventually (eventually_ge_atTop 0)
  filter_upwards [hsharp, hdomRaw, hlogNonneg, hllNonneg] with
      M hsharpM hdomM hlogM hllM
  apply hsharpM.trans
  simp only [Function.comp_apply, Real.norm_eq_abs] at hdomM
  rw [abs_of_nonneg
      (Real.rpow_nonneg hllM (Real.log 4)),
    abs_of_nonneg (Real.rpow_nonneg hlogM (1 / 2 : ℝ))] at hdomM
  exact hdomM

theorem eventually_engelsmaMaynardModulus_le_sqrt_log_sub :
    ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardModulus N : ℝ) ≤
        Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (1 / 2 : ℝ) := by
  simpa [engelsmaMaynardModulus] using
    (tendsto_sub_atTop_nat 1).eventually
      eventually_primorial_tripleLogCutoff_le_sqrt_log

theorem eventually_log_engelsmaMaynardRadius_ge_half
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (alpha / 2) * Real.log ((N - 1 : ℕ) : ℝ) ≤
        Real.log (engelsmaMaynardRadius alpha N) := by
  have hM : Tendsto (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlogM : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hM
  have hx : Tendsto
      (fun N : ℕ => Real.rpow ((N - 1 : ℕ) : ℝ) alpha) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp hM
  have hlogLarge : ∀ᶠ N : ℕ in atTop,
      Real.log 2 ≤ (alpha / 2) *
        Real.log ((N - 1 : ℕ) : ℝ) := by
    have hscaled : Tendsto
        (fun x : ℝ => (alpha / 2) * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by positivity)).2 tendsto_id
    exact (hscaled.comp hlogM).eventually (eventually_ge_atTop (Real.log 2))
  filter_upwards [hx.eventually (eventually_ge_atTop 2), hlogLarge,
    eventually_ge_atTop 3] with N hxTwo hlogLargeN hN
  let x := Real.rpow ((N - 1 : ℕ) : ℝ) alpha
  have hMpos : (0 : ℝ) < (N - 1 : ℕ) := by
    exact_mod_cast (show 0 < N - 1 by omega)
  have hxPos : 0 < x := Real.rpow_pos_of_pos hMpos alpha
  have hfloor : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hsub : x / 2 ≤ x - 1 := by linarith
    exact hsub.trans (le_of_lt (Nat.sub_one_lt_floor x))
  have hfloorPos : (0 : ℝ) < (⌊x⌋₊ : ℝ) :=
    (div_pos hxPos (by norm_num)).trans_le hfloor
  have hlogFloor : Real.log (x / 2) ≤ Real.log (⌊x⌋₊ : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by exact div_pos hxPos (by norm_num)) hfloorPos hfloor
  have hlogx : Real.log x =
      alpha * Real.log ((N - 1 : ℕ) : ℝ) := by
    unfold x
    simpa using Real.log_rpow hMpos alpha
  have hlower : (alpha / 2) * Real.log ((N - 1 : ℕ) : ℝ) ≤
      Real.log (x / 2) := by
    rw [Real.log_div hxPos.ne' (by norm_num), hlogx]
    linarith
  unfold engelsmaMaynardRadius maynardDivisorCutoff
  exact hlower.trans hlogFloor

theorem eventually_sqrt_log_sub_le_half_alpha_log
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (1 / 2 : ℝ) ≤
        (alpha / 2) * Real.log ((N - 1 : ℕ) : ℝ) := by
  have hlogM : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hinv := (tendsto_rpow_neg_atTop
    (show (0 : ℝ) < 1 / 2 by norm_num)).comp hlogM
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (-(1 / 2 : ℝ)) ≤
        alpha / 2 :=
    hinv.eventually (eventually_le_nhds (by positivity))
  have hlogPos : ∀ᶠ N : ℕ in atTop,
      0 < Real.log ((N - 1 : ℕ) : ℝ) :=
    hlogM.eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall, hlogPos] with N hsmallN hlogPosN
  let L := Real.log ((N - 1 : ℕ) : ℝ)
  calc
    Real.rpow L (1 / 2 : ℝ) =
        L * Real.rpow L (-(1 / 2 : ℝ)) := by
      symm
      calc
        L * Real.rpow L (-(1 / 2 : ℝ)) =
            Real.rpow L 1 * Real.rpow L (-(1 / 2 : ℝ)) := by
          exact congrArg (fun z : ℝ => z * Real.rpow L (-(1 / 2 : ℝ)))
            (Real.rpow_one L).symm
        _ = Real.rpow L (1 + (-(1 / 2 : ℝ))) :=
          (Real.rpow_add hlogPosN 1 (-(1 / 2 : ℝ))).symm
        _ = Real.rpow L (1 / 2 : ℝ) := by
          congr 1
          ring
    _ ≤ L * (alpha / 2) :=
      mul_le_mul_of_nonneg_left hsmallN hlogPosN.le
    _ = (alpha / 2) * L := by ring

theorem eventually_engelsmaMaynardModulus_le_logRadius
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardModulus N : ℝ) ≤
        Real.log (engelsmaMaynardRadius alpha N) := by
  filter_upwards [eventually_engelsmaMaynardModulus_le_sqrt_log_sub,
    eventually_sqrt_log_sub_le_half_alpha_log halpha,
    eventually_log_engelsmaMaynardRadius_ge_half halpha] with
      N hW hsqrt hR
  exact hW.trans (hsqrt.trans hR)

theorem eventually_engelsmaMaynardCrossBound_conditions
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      0 < engelsmaMaynardRadius alpha N ∧
      0 < tripleLogCutoff (N - 1) ∧
      (engelsmaMaynardModulus N : ℝ) ≤
        1 + Real.log (engelsmaMaynardRadius alpha N) := by
  have hRlog := eventually_log_engelsmaMaynardRadius_ge_half halpha
  have hDbase : ∀ᶠ M : ℕ in atTop, 1 ≤ tripleLogCutoff M := by
    obtain ⟨M₀, hM₀⟩ := exists_tripleLogCutoff_ge 1
    exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  have hD := (tendsto_sub_atTop_nat 1).eventually hDbase
  filter_upwards [hRlog, hD,
    eventually_engelsmaMaynardModulus_le_logRadius halpha,
    eventually_ge_atTop 3] with N hRlogN hDN hW hN
  have hlogMpos : 0 < Real.log ((N - 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N - 1 by omega)
  have hRlogPos : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    lt_of_lt_of_le (mul_pos (by positivity) hlogMpos) hRlogN
  have hRone : (1 : ℝ) < engelsmaMaynardRadius alpha N :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hRlogPos
  have hRoneNat : 1 < engelsmaMaynardRadius alpha N := by
    exact_mod_cast hRone
  exact ⟨Nat.zero_lt_of_lt hRoneNat,
    Nat.zero_lt_of_lt hDN, hW.trans (by linarith)⟩

end BoundedGaps.Maynard
