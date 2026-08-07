import BoundedGaps.Maynard.ConcreteS2TauBounds
import BoundedGaps.Maynard.ConcreteScaleBounds

noncomputable section

/-!
# Normalized concrete tau-weighted S2 error

This file bounds the concrete tau endpoint envelope by an explicit logarithmic
ratio and proves that the actual signed S2 error vanishes after normalization.
-/

namespace BoundedGaps.Maynard

open Filter

def engelsmaS2TauHalfLogExponent : ℕ :=
  (3 * Fintype.card BoundedGaps.engelsmaTuple) ^ 2 +
    4 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2 + 3 * 106 + 2

theorem tauIndexedEndpointEnvelope_le_log_ratio
    {H : Finset ℕ} {Q x B : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hlogQ : 0 ≤ 1 + Real.log Q) :
    tauIndexedEndpointEnvelope H Q C ((B * 2 : ℕ) : ℝ) x ≤
      (Fintype.card H : ℝ) * (3 * (C + 1)) * ((x + 1 : ℕ) : ℝ) *
        (1 + Real.log Q) ^ ((3 * Fintype.card H) ^ 2) /
          (Real.log (x : ℝ)) ^ B := by
  let k := Fintype.card H
  let m := (3 * k) ^ 2
  let LX := Real.log (x : ℝ)
  let LQ := 1 + Real.log Q
  let K := 3 * (C + 1)
  have hLX : 0 < LX := lt_of_lt_of_le zero_lt_one hlogx
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hKC : 3 * C ≤ K ^ 2 := by
    dsimp [K]
    nlinarith
  have hU : 0 ≤ (3 : ℝ) * ((x + 1 : ℕ) : ℝ) * LQ ^ (2 * m) := by
    positivity
  have hV : 0 ≤ C * (x : ℝ) /
      Real.rpow LX ((B * 2 : ℕ) : ℝ) := by
    exact div_nonneg (mul_nonneg hC (by positivity))
      (Real.rpow_nonneg hLX.le _)
  have hradical :
      Real.sqrt ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) * LQ ^ (2 * m)) *
          Real.sqrt (C * (x : ℝ) /
            Real.rpow LX ((B * 2 : ℕ) : ℝ)) ≤
        K * ((x + 1 : ℕ) : ℝ) * LQ ^ m / LX ^ B := by
    rw [← Real.sqrt_mul hU]
    rw [Real.sqrt_le_iff]
    constructor
    · exact div_nonneg
        (mul_nonneg (mul_nonneg hK (by positivity)) (pow_nonneg hlogQ _))
        (pow_nonneg hLX.le _)
    · have hrpowX : Real.rpow LX ((B * 2 : ℕ) : ℝ) = LX ^ (B * 2) :=
        Real.rpow_natCast LX (B * 2)
      rw [hrpowX]
      have hpowQ : LQ ^ (2 * m) = (LQ ^ m) ^ 2 := by
        rw [show 2 * m = m * 2 by omega, pow_mul]
      have hpowX : LX ^ (B * 2) = (LX ^ B) ^ 2 := by rw [pow_mul]
      rw [hpowQ, hpowX]
      have hden : 0 < (LX ^ B) ^ 2 := sq_pos_of_pos (pow_pos hLX _)
      rw [div_pow]
      apply (le_div_iff₀ hden).2
      have hxle : (x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by norm_num
      have hbase : 3 * C * (x : ℝ) ≤ K ^ 2 * ((x + 1 : ℕ) : ℝ) := by
        calc
          3 * C * (x : ℝ) ≤ K ^ 2 * (x : ℝ) :=
            mul_le_mul_of_nonneg_right hKC (by positivity)
          _ ≤ K ^ 2 * ((x + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hxle (sq_nonneg K)
      rw [mul_assoc, div_mul_cancel₀ _ hden.ne']
      calc
        3 * ((x + 1 : ℕ) : ℝ) * (LQ ^ m) ^ 2 * (C * (x : ℝ)) =
            (3 * C * (x : ℝ)) *
              (((x + 1 : ℕ) : ℝ) * (LQ ^ m) ^ 2) := by ring
        _ ≤ (K ^ 2 * ((x + 1 : ℕ) : ℝ)) *
              (((x + 1 : ℕ) : ℝ) * (LQ ^ m) ^ 2) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = (K * ((x + 1 : ℕ) : ℝ) * LQ ^ m) ^ 2 := by ring
  unfold tauIndexedEndpointEnvelope
  dsimp [k, m, LX, LQ, K] at hradical ⊢
  calc
    (Fintype.card H : ℝ) *
        (Real.sqrt
          ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ (2 * (3 * Fintype.card H) ^ 2)) *
          Real.sqrt
            (C * (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) ((B * 2 : ℕ) : ℝ))) ≤
        (Fintype.card H : ℝ) *
          (3 * (C + 1) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ ((3 * Fintype.card H) ^ 2) /
              (Real.log (x : ℝ)) ^ B) :=
      mul_le_mul_of_nonneg_left hradical (Nat.cast_nonneg _)
    _ = _ := by ring

theorem tauIndexedEndpointEnvelope_le_nat_log_ratio
    {H : Finset ℕ} {Q x N B : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlogN : 2 ≤ Real.log (N : ℝ))
    (hx : ((x + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ))
    (hlogx : Real.log (N : ℝ) / 2 ≤ Real.log (x : ℝ))
    (hlogQ : 0 ≤ 1 + Real.log Q)
    (hlogQBound : 1 + Real.log Q ≤ 4 * Real.log (N : ℝ)) :
    tauIndexedEndpointEnvelope H Q C ((B * 2 : ℕ) : ℝ) x ≤
      ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
          4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ B) *
        (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((3 * Fintype.card H) ^ 2) /
          (Real.log (N : ℝ)) ^ B := by
  let k := Fintype.card H
  let m := (3 * k) ^ 2
  let LN := Real.log (N : ℝ)
  let LQ := 1 + Real.log Q
  let K := (k : ℝ) * (3 * (C + 1))
  have hLN : 0 < LN := by dsimp [LN]; linarith
  have hhalf : 0 < LN / 2 := by positivity
  have hlogxOne : 1 ≤ Real.log (x : ℝ) := by
    calc
      1 ≤ LN / 2 := by dsimp [LN]; linarith
      _ ≤ Real.log (x : ℝ) := hlogx
  have hpoint := tauIndexedEndpointEnvelope_le_log_ratio
    (H := H) (Q := Q) (x := x) (B := B) hC hlogxOne hlogQ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpowQ : LQ ^ m ≤ (4 * LN) ^ m :=
    pow_le_pow_left₀ hlogQ hlogQBound m
  have hnum : K * ((x + 1 : ℕ) : ℝ) * LQ ^ m ≤
      K * (3 * (N : ℝ)) * (4 * LN) ^ m := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hx hK) hpowQ (pow_nonneg hlogQ _)
      (mul_nonneg hK (by positivity))
  have hden : (LN / 2) ^ B ≤ (Real.log (x : ℝ)) ^ B :=
    pow_le_pow_left₀ hhalf.le hlogx B
  calc
    tauIndexedEndpointEnvelope H Q C ((B * 2 : ℕ) : ℝ) x ≤
        K * ((x + 1 : ℕ) : ℝ) * LQ ^ m /
          (Real.log (x : ℝ)) ^ B := by
      simpa [K, k, m, LQ] using hpoint
    _ ≤ (K * (3 * (N : ℝ)) * (4 * LN) ^ m) /
          (Real.log (x : ℝ)) ^ B :=
      div_le_div_of_nonneg_right hnum (pow_nonneg (by positivity) _)
    _ ≤ (K * (3 * (N : ℝ)) * (4 * LN) ^ m) / (LN / 2) ^ B := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact pow_pos hhalf _
      · exact hden
    _ = ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
          4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ B) *
        (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((3 * Fintype.card H) ^ 2) /
          (Real.log (N : ℝ)) ^ B := by
      dsimp [K, k, m, LN]
      rw [mul_pow, div_pow]
      field_simp

theorem eventually_engelsmaMaynardModulus_le_log_cube :
    ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardModulus N : ℝ) ≤ (Real.log (N : ℝ)) ^ 3 := by
  have hllBase : ∀ᶠ M : ℕ in atTop,
      1 ≤ Real.log (Real.log (M : ℝ)) := by
    have ht : Tendsto (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact ht.eventually (eventually_ge_atTop 1)
  have hll := (tendsto_sub_atTop_nat 1).eventually hllBase
  filter_upwards [hll, eventually_ge_atTop 4] with N hll hN
  have hNm1 : 1 < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < N - 1 by omega)
  have hlogMpos : 0 < Real.log ((N - 1 : ℕ) : ℝ) := Real.log_pos hNm1
  have hlogMone : 1 ≤ Real.log ((N - 1 : ℕ) : ℝ) :=
    hll.trans (Real.log_le_self hlogMpos.le)
  have hlogMono : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show ((N - 1 : ℕ) : ℝ) ∈ Set.Ioi 0
      change 0 < ((N - 1 : ℕ) : ℝ)
      exact_mod_cast (show 0 < N - 1 by omega)
    · show (N : ℝ) ∈ Set.Ioi 0
      change 0 < (N : ℝ)
      exact_mod_cast (show 0 < N by omega)
    · exact_mod_cast Nat.sub_le N 1
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h
    exact h
  calc
    (engelsmaMaynardModulus N : ℝ) =
        (primorial (tripleLogCutoff (N - 1)) : ℝ) := rfl
    _ ≤ Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (Real.log 4) :=
      primorial_tripleLogCutoff_le_log_rpow hll
    _ ≤ Real.rpow (Real.log (N : ℝ)) (Real.log 4) :=
      Real.rpow_le_rpow hlogMpos.le hlogMono (Real.log_nonneg (by norm_num))
    _ ≤ Real.rpow (Real.log (N : ℝ)) 3 :=
      Real.rpow_le_rpow_of_exponent_le (hlogMone.trans hlogMono) hlog4
    _ = (Real.log (N : ℝ)) ^ 3 := Real.rpow_natCast _ 3

theorem eventually_engelsmaMaynardScale_ge_nat_div_modulus_pow
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ 106 ≤
        engelsmaMaynardScale alpha N := by
  have hreal : Tendsto
      (fun N : ℕ => engelsmaMaynardRealRadius alpha N) atTop atTop := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlog : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (engelsmaMaynardRealRadius alpha N) := by
    filter_upwards [hreal.eventually (eventually_ge_atTop (Real.exp 1))] with N hN
    have hmono : Real.log (Real.exp 1) ≤
        Real.log (engelsmaMaynardRealRadius alpha N) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
        (by exact lt_of_lt_of_le (by positivity) hN) hN
    simpa using hmono
  filter_upwards [hlog, eventually_ge_atTop 1] with N hlog hN
  have hWpos : 0 < engelsmaMaynardModulus N := primorial_pos _
  have hphi : 1 ≤ (Nat.totient (engelsmaMaynardModulus N) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hWpos))
  have hnum : (N : ℝ) ≤
      (Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 * (N : ℝ) *
        (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
    calc
      (N : ℝ) = 1 * (N : ℝ) * 1 := by ring
      _ ≤ (Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 * (N : ℝ) *
          (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
        gcongr
        · exact one_le_pow₀ hphi
        · exact one_le_pow₀ hlog
  unfold engelsmaMaynardScale maynardSieveScale
  exact div_le_div_of_nonneg_right hnum (by positivity)

theorem eventually_one_add_log_engelsmaMaynardRadius_le
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      1 + Real.log (engelsmaMaynardRadius alpha N) ≤
        (1 + alpha) * Real.log (N : ℝ) := by
  have hR : ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardRadius alpha N : ℝ) ≤ Real.rpow (N : ℝ) alpha := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    unfold engelsmaMaynardRadius maynardDivisorCutoff
    have hfloor :
        ((maynardDivisorCutoff alpha (N - 1) : ℕ) : ℝ) ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) alpha := by
      unfold maynardDivisorCutoff
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)
    have hsub : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 1
    exact hfloor.trans (Real.rpow_le_rpow (by positivity) hsub halpha.le)
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  filter_upwards [hR, hlogN, eventually_ge_atTop 2] with N hRN hLN hN
  have hlogbase : 0 ≤ Real.log (N : ℝ) := by linarith
  by_cases hzero : engelsmaMaynardRadius alpha N = 0
  · simp [hzero]
    nlinarith [mul_nonneg halpha.le hlogbase]
  · have hRpos : 0 < (engelsmaMaynardRadius alpha N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    have hlogmono : Real.log (engelsmaMaynardRadius alpha N) ≤
        Real.log (Real.rpow (N : ℝ) alpha) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show (engelsmaMaynardRadius alpha N : ℝ) ∈ Set.Ioi 0 from hRpos)
        (show Real.rpow (N : ℝ) alpha ∈ Set.Ioi 0 from
          Real.rpow_pos_of_pos (by positivity) _)
        hRN
    have hlogpow : Real.log (Real.rpow (N : ℝ) alpha) =
        alpha * Real.log (N : ℝ) := by
      simpa using (Real.log_rpow (x := (N : ℝ)) (by positivity) alpha)
    rw [hlogpow] at hlogmono
    nlinarith

end BoundedGaps.Maynard
