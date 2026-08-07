import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaShallowCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar scales for the Siegel--Walfisz character estimate

This file formalizes the source height `exp (sqrt (log x))` and the elementary
real inequalities used to insert it into the explicit formula and the
exceptional/nonexceptional zero estimates.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, proof of Theorem 12.4,
printed p. 122. Semantic review: `SEM-564`.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable section

/-- The truncation height chosen in the proof of Koukoulopoulos Theorem 12.4. -/
noncomputable def siegelWalfiszHeight (x : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (x : ℝ)))

/-- Eventually the source height lies in the explicit-formula range, dominates
every fixed logarithmic modulus power, and absorbs the two polynomial factors
left by SEM-535 and SEM-537. -/
theorem eventually_siegelWalfiszHeight_conditions
    (D : ℝ) (_hD : 0 < D) (M : ℕ) (hM : 2 ≤ M) :
    ∀ᶠ x : ℕ in Filter.atTop,
      4 ≤ x ∧
        1 ≤ Real.log (x : ℝ) ∧
          2 ≤ siegelWalfiszHeight x ∧
            siegelWalfiszHeight x ≤ (x : ℝ) ∧
              Real.log (x : ℝ) ^ D ≤ siegelWalfiszHeight x ∧
                4 * Real.sqrt (Real.log (x : ℝ)) ^ 4 ≤
                    Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) ∧
                  16 * Real.sqrt (Real.log (x : ℝ)) ^ 2 ≤
                    Real.exp (Real.sqrt (Real.log (x : ℝ)) /
                      (8 * (M : ℝ) ^ 2)) := by
  have hxTop : Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hxTop
  have huTop : Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hLTop
  have hheightTwo : ∀ᶠ x : ℕ in atTop, 2 ≤ siegelWalfiszHeight x := by
    exact (Real.tendsto_exp_atTop.comp huTop).eventually
      (eventually_ge_atTop 2)
  have hmodulus : ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ D ≤ siegelWalfiszHeight x := by
    have hdom := ((isLittleO_rpow_exp_atTop (2 * D)).comp_tendsto huTop).eventuallyLE
    filter_upwards [hdom,
      hLTop.eventually (eventually_ge_atTop (0 : ℝ))] with x hdomx hLx
    let L : ℝ := Real.log (x : ℝ)
    let u : ℝ := Real.sqrt L
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have husq : u ^ 2 = L := by
      dsimp [u]
      exact Real.sq_sqrt (by simpa [L] using hLx)
    have hpow : L ^ D = u ^ (2 * D) := by
      calc
        L ^ D = (u ^ 2) ^ D := by rw [husq]
        _ = (u ^ (2 : ℝ)) ^ D := by rw [Real.rpow_two]
        _ = u ^ (2 * D) := (Real.rpow_mul hu0 2 D).symm
    simp only [Function.comp_apply, Real.norm_eq_abs] at hdomx
    rw [abs_of_nonneg (Real.rpow_nonneg hu0 (2 * D)),
      abs_of_pos (Real.exp_pos u)] at hdomx
    simpa [L, u, siegelWalfiszHeight, hpow] using hdomx
  have hfour : ∀ᶠ x : ℕ in atTop,
      4 * Real.sqrt (Real.log (x : ℝ)) ^ 4 ≤
        Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) := by
    have hdom := (((isLittleO_pow_exp_pos_mul_atTop 4
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left 4).comp_tendsto
        huTop).eventuallyLE
    filter_upwards [hdom] with x hdomx
    let u : ℝ := Real.sqrt (Real.log (x : ℝ))
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hleft : 0 ≤ 4 * u ^ 4 := by positivity
    simp only [Function.comp_apply, Real.norm_eq_abs] at hdomx
    rw [abs_of_nonneg hleft,
      abs_of_pos (Real.exp_pos ((1 / 2 : ℝ) * u))] at hdomx
    simpa [u, div_eq_mul_inv, mul_comm] using hdomx
  have hb : 0 < (1 / (8 * (M : ℝ) ^ 2) : ℝ) := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
    positivity
  have hsixteen : ∀ᶠ x : ℕ in atTop,
      16 * Real.sqrt (Real.log (x : ℝ)) ^ 2 ≤
        Real.exp (Real.sqrt (Real.log (x : ℝ)) /
          (8 * (M : ℝ) ^ 2)) := by
    have hlittle := (isLittleO_pow_exp_pos_mul_atTop 2 hb).const_mul_left 16
    have hdom := (hlittle.comp_tendsto huTop).eventuallyLE
    filter_upwards [hdom] with x hdomx
    let u : ℝ := Real.sqrt (Real.log (x : ℝ))
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hleft : 0 ≤ 16 * u ^ 2 := by positivity
    simp only [Function.comp_apply, Real.norm_eq_abs] at hdomx
    rw [abs_of_nonneg hleft,
      abs_of_pos (Real.exp_pos ((1 / (8 * (M : ℝ) ^ 2)) * u))] at hdomx
    simpa [u, div_eq_mul_inv, mul_comm] using hdomx
  filter_upwards [eventually_ge_atTop 4,
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)), hheightTwo,
    hmodulus, hfour, hsixteen] with x hx hL hheight hmodulus hfour hsixteen
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have huL : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have hsquare := Real.sq_sqrt (zero_le_one.trans hL)
    have hu := Real.one_le_sqrt.mpr hL
    nlinarith
  have hheightX : siegelWalfiszHeight x ≤ (x : ℝ) := by
    calc
      siegelWalfiszHeight x ≤ Real.exp (Real.log (x : ℝ)) := by
        exact Real.exp_monotone huL
      _ = (x : ℝ) := Real.exp_log hxpos
  exact ⟨hx, hL, hheight, hheightX, hmodulus, hfour, hsixteen⟩

/-- Once `log x >= 1` and `q` is below the source height, the logarithm in the
nonexceptional zero estimate is positive and at most `4 * sqrt (log x)`. -/
theorem log_modulus_mul_siegelWalfiszHeight_add_two_bounds
    {x q : ℕ} [NeZero q]
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq : (q : ℝ) ≤ siegelWalfiszHeight x) :
    0 < Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ∧
      Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ≤
        4 * Real.sqrt (Real.log (x : ℝ)) := by
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  let T : ℝ := Real.exp u
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_sqrt.mpr hxlog
  have hTtwo : 2 < T := by
    dsimp [T]
    exact Real.exp_one_gt_two.trans_le (Real.exp_monotone hu)
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.pos q
  have hprodOne : 1 < (q : ℝ) * (T + 2) := by
    have hTadd : 1 < T + 2 := by linarith
    nlinarith [mul_le_mul hqone hTadd.le (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (q : ℝ))]
  have hTadd : T + 2 ≤ 3 * T := by linarith
  have hTsqThree : 3 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 2)]
  have hprodPow : (q : ℝ) * (T + 2) ≤ T ^ 4 := by
    calc
      (q : ℝ) * (T + 2) ≤ T * (T + 2) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      _ ≤ T * (3 * T) := mul_le_mul_of_nonneg_left hTadd (by positivity)
      _ = 3 * T ^ 2 := by ring
      _ ≤ T ^ 2 * T ^ 2 :=
        mul_le_mul_of_nonneg_right hTsqThree (sq_nonneg T)
      _ = T ^ 4 := by ring
  have hlogT : Real.log T = u := by simp [T]
  constructor
  · exact Real.log_pos hprodOne
  · have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) * (T + 2))
      hprodPow
    rw [Real.log_pow, hlogT] at hlog
    simpa [u, T, siegelWalfiszHeight] using hlog

/-- At the source height, the explicit-formula remainder has exponential
decay once its fourth-power logarithmic factor has been absorbed. -/
theorem mul_dirichletExplicitFormulaErrorScale_siegelWalfiszHeight_le
    (K : ℝ) (hK : 0 ≤ K) {x q : ℕ} [NeZero q]
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq : (q : ℝ) ≤ siegelWalfiszHeight x)
    (habsorb : 4 * Real.sqrt (Real.log (x : ℝ)) ^ 4 ≤
      Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2)) :
    K * dirichletExplicitFormulaErrorScale
        (x : ℝ) q (siegelWalfiszHeight x) ≤
      K * ((x : ℝ) * Real.exp
        (-(1 / 2 : ℝ) * Real.sqrt (Real.log (x : ℝ)))) := by
  let L : ℝ := Real.log (x : ℝ)
  let u : ℝ := Real.sqrt L
  let T : ℝ := Real.exp u
  have hL : 1 ≤ L := by simpa [L] using hxlog
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_sqrt.mpr hL
  have huL : u ≤ L := by
    have husq : u ^ 2 = L := by
      dsimp [u]
      exact Real.sq_sqrt (zero_le_one.trans hL)
    nlinarith
  have hxone : (1 : ℝ) < x := by
    exact (Real.log_pos_iff (Nat.cast_nonneg x)).mp
      (zero_lt_one.trans_le hxlog)
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hxone
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqT : (q : ℝ) ≤ T := by
    simpa [T, u, L, siegelWalfiszHeight] using hq
  have hlogqNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlogq : Real.log (q : ℝ) ≤ u := by
    calc
      Real.log (q : ℝ) ≤ Real.log T := Real.log_le_log hqpos hqT
      _ = u := by simp [T]
  have hlogProductNonneg : 0 ≤ Real.log ((x : ℝ) * q) := by
    rw [Real.log_mul hxpos.ne' hqpos.ne']
    exact add_nonneg (zero_le_one.trans hL) hlogqNonneg
  have hlogProduct : Real.log ((x : ℝ) * q) ≤ 2 * L := by
    rw [Real.log_mul hxpos.ne' hqpos.ne']
    linarith
  have hlogSquare : Real.log ((x : ℝ) * q) ^ 2 ≤ 4 * u ^ 4 := by
    have hsquare := pow_le_pow_left₀ hlogProductNonneg hlogProduct 2
    have husq : u ^ 2 = L := by
      dsimp [u]
      exact Real.sq_sqrt (zero_le_one.trans hL)
    calc
      Real.log ((x : ℝ) * q) ^ 2 ≤ (2 * L) ^ 2 := hsquare
      _ = 4 * u ^ 4 := by rw [← husq]; ring
  have habsorb' : 4 * u ^ 4 ≤ Real.exp (u / 2) := by
    simpa [u, L] using habsorb
  have hTpos : 0 < T := by positivity
  rw [dirichletExplicitFormulaErrorScale]
  calc
    K * ((x : ℝ) * Real.log ((x : ℝ) * q) ^ 2 / T) ≤
        K * ((x : ℝ) * (4 * u ^ 4) / T) := by
      gcongr
    _ ≤ K * ((x : ℝ) * Real.exp (u / 2) / T) := by
      gcongr
    _ = K * ((x : ℝ) * Real.exp (-(1 / 2 : ℝ) * u)) := by
      change K * ((x : ℝ) * Real.exp (u / 2) / Real.exp u) = _
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        K * ((x : ℝ) * Real.exp (u / 2) * Real.exp (-u)) =
            K * ((x : ℝ) * (Real.exp (u / 2) * Real.exp (-u))) := by ring
        _ = K * ((x : ℝ) * Real.exp (u / 2 + -u)) := by
          rw [← Real.exp_add]
        _ = K * ((x : ℝ) * Real.exp (-(1 / 2 : ℝ) * u)) := by
          congr 3
          ring
    _ = K * ((x : ℝ) * Real.exp
        (-(1 / 2 : ℝ) * Real.sqrt (Real.log (x : ℝ)))) := by
      rfl

/-- At the source height, the complete SEM-537 nonexceptional envelope has
exponential decay after its squared-log factor is absorbed. -/
theorem dirichletNonexceptionalSiegelWalfiszEnvelope_le
    (A M : ℕ) (hM : 2 ≤ M) {x q : ℕ} [NeZero q]
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq : (q : ℝ) ≤ siegelWalfiszHeight x)
    (habsorb : 16 * Real.sqrt (Real.log (x : ℝ)) ^ 2 ≤
      Real.exp (Real.sqrt (Real.log (x : ℝ)) /
        (8 * (M : ℝ) ^ 2))) :
    96 * (A : ℝ) *
        (x : ℝ) ^ (1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)))) *
            Real.log ((q : ℝ) * (siegelWalfiszHeight x + 2)) ^ 2 ≤
      96 * (A : ℝ) * ((x : ℝ) * Real.exp
        (-(1 / (8 * (M : ℝ) ^ 2)) *
          Real.sqrt (Real.log (x : ℝ)))) := by
  let L : ℝ := Real.log (x : ℝ)
  let u : ℝ := Real.sqrt L
  let T : ℝ := Real.exp u
  let m : ℝ := (M : ℝ) ^ 2
  let V : ℝ := Real.log ((q : ℝ) * (T + 2))
  have hL : 1 ≤ L := by simpa [L] using hxlog
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_sqrt.mpr hL
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have husq : u ^ 2 = L := by
    dsimp [u]
    exact Real.sq_sqrt (zero_le_one.trans hL)
  have hmpos : 0 < m := by
    dsimp [m]
    positivity
  have hxone : (1 : ℝ) < x := by
    exact (Real.log_pos_iff (Nat.cast_nonneg x)).mp
      (zero_lt_one.trans_le hxlog)
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hxone
  have hVbounds : 0 < V ∧ V ≤ 4 * u := by
    simpa [V, T, u, L, siegelWalfiszHeight] using
      (log_modulus_mul_siegelWalfiszHeight_add_two_bounds hxlog hq)
  have hden : 0 < m * V := mul_pos hmpos hVbounds.1
  have hdenUpper : m * V ≤ 4 * m * u := by
    calc
      m * V ≤ m * (4 * u) :=
        mul_le_mul_of_nonneg_left hVbounds.2 hmpos.le
      _ = 4 * m * u := by ring
  have hreciprocal : 1 / (4 * m * u) ≤ 1 / (m * V) :=
    one_div_le_one_div_of_le (by positivity) hdenUpper
  have hscaledReciprocal :
      L * (1 / (4 * m * u)) ≤ L * (1 / (m * V)) :=
    mul_le_mul_of_nonneg_left hreciprocal (zero_le_one.trans hL)
  have hcancel : L * (1 / (4 * m * u)) = u / (4 * m) := by
    rw [← husq]
    field_simp [hmpos.ne', hupos.ne']
  have hlogExponent :
      L * (1 - 1 / (m * V)) ≤ L - u / (4 * m) := by
    calc
      L * (1 - 1 / (m * V)) = L - L * (1 / (m * V)) := by ring
      _ ≤ L - L * (1 / (4 * m * u)) :=
        sub_le_sub_left hscaledReciprocal L
      _ = L - u / (4 * m) := by rw [hcancel]
  have hxpower :
      (x : ℝ) ^ (1 - 1 / (m * V)) ≤
        (x : ℝ) * Real.exp (-(u / (4 * m))) := by
    rw [Real.rpow_def_of_pos hxpos]
    calc
      Real.exp (Real.log (x : ℝ) * (1 - 1 / (m * V))) ≤
          Real.exp (L - u / (4 * m)) := by
        apply Real.exp_monotone
        simpa [L] using hlogExponent
      _ = Real.exp L * Real.exp (-(u / (4 * m))) := by
        rw [show L - u / (4 * m) = L + -(u / (4 * m)) by ring,
          Real.exp_add]
      _ = (x : ℝ) * Real.exp (-(u / (4 * m))) := by
        change Real.exp (Real.log (x : ℝ)) * Real.exp (-(u / (4 * m))) = _
        rw [Real.exp_log hxpos]
  have hVsquare : V ^ 2 ≤ 16 * u ^ 2 := by
    have hsquare := pow_le_pow_left₀ hVbounds.1.le hVbounds.2 2
    calc
      V ^ 2 ≤ (4 * u) ^ 2 := hsquare
      _ = 16 * u ^ 2 := by ring
  have habsorb' : 16 * u ^ 2 ≤ Real.exp (u / (8 * m)) := by
    simpa [u, L, m] using habsorb
  change 96 * (A : ℝ) *
      (x : ℝ) ^ (1 - 1 / (m * V)) * V ^ 2 ≤ _
  calc
    96 * (A : ℝ) * (x : ℝ) ^ (1 - 1 / (m * V)) * V ^ 2 ≤
        96 * (A : ℝ) *
          ((x : ℝ) * Real.exp (-(u / (4 * m)))) * V ^ 2 := by
      gcongr
    _ ≤ 96 * (A : ℝ) *
          ((x : ℝ) * Real.exp (-(u / (4 * m)))) * (16 * u ^ 2) := by
      gcongr
    _ ≤ 96 * (A : ℝ) *
          ((x : ℝ) * Real.exp (-(u / (4 * m)))) *
            Real.exp (u / (8 * m)) := by
      gcongr
    _ = 96 * (A : ℝ) * ((x : ℝ) *
        Real.exp (-(1 / (8 * m)) * u)) := by
      calc
        96 * (A : ℝ) * ((x : ℝ) * Real.exp (-(u / (4 * m)))) *
            Real.exp (u / (8 * m)) =
          96 * (A : ℝ) * ((x : ℝ) *
            (Real.exp (-(u / (4 * m))) * Real.exp (u / (8 * m)))) := by ring
        _ = 96 * (A : ℝ) * ((x : ℝ) *
            Real.exp (-(u / (4 * m)) + u / (8 * m))) := by
          rw [← Real.exp_add]
        _ = 96 * (A : ℝ) * ((x : ℝ) *
            Real.exp (-(1 / (8 * m)) * u)) := by
          congr 3
          ring
    _ = 96 * (A : ℝ) * ((x : ℝ) * Real.exp
        (-(1 / (8 * (M : ℝ) ^ 2)) *
          Real.sqrt (Real.log (x : ℝ)))) := by
      rfl

end

end BoundedGaps.Maynard
