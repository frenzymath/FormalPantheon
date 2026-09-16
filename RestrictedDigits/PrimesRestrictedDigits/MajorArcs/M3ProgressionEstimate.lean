import PrimesRestrictedDigits.MajorArcs.M3Progression
import PrimesRestrictedDigits.MajorArcs.M2Absorption

/-!
# Uniform weighted M3 progression estimate

This aggregates the exact two-prefix representation against the projected
harmonic mass and inserts the strict prime-log progression theorem.
-/

open scoped BigOperators
open Filter

namespace PrimesRestrictedDigits

private theorem eventually_majorArcM3ScalarBounds
    (D R : Nat) {eta : Real} (heta : 0 < eta)
    (C xPNT : Real) :
    let H : Nat := 4 * D + R + 1
    let c : Real := eta / 4
    let A : Real := 4 * C / c ^ H * (2 * Real.log 4) ^ R
    ∀ᶠ x : Real in atTop,
      (4 : Real) <= x ∧
      xPNT <= x ^ c ∧
      Real.log x ^ D <= (c * Real.log x) ^ (D + 1) ∧
      Real.exp (Real.exp (12 / eta ^ 2)) <= x ∧
      5 < x ^ c ∧
      A <= Real.log x := by
  dsimp only
  have hc : 0 < eta / 4 := by positivity
  have hcPow : 0 < (eta / 4) ^ (D + 1) := pow_pos hc _
  have hpnt := (tendsto_rpow_atTop hc).eventually_ge_atTop xPNT
  have hfive := (tendsto_rpow_atTop hc).eventually_gt_atTop 5
  have hlogScale := Real.tendsto_log_atTop.eventually_ge_atTop
    (((eta / 4) ^ (D + 1))⁻¹)
  have hlogA := Real.tendsto_log_atTop.eventually_ge_atTop
    (4 * C / (eta / 4) ^ (4 * D + R + 1) *
      (2 * Real.log 4) ^ R)
  filter_upwards [eventually_ge_atTop (4 : Real), hpnt, hlogScale,
    eventually_ge_atTop (Real.exp (Real.exp (12 / eta ^ 2))),
    hfive, hlogA] with x hx4 hxPNT hxLogScale hxExp hxFive hxA
  have hxOne : 1 <= x := by linarith
  have hlogNonneg : 0 <= Real.log x := Real.log_nonneg hxOne
  have hscale : 1 <= (eta / 4) ^ (D + 1) * Real.log x := by
    calc
      1 = (eta / 4) ^ (D + 1) * ((eta / 4) ^ (D + 1))⁻¹ := by
        field_simp
      _ <= (eta / 4) ^ (D + 1) * Real.log x :=
        mul_le_mul_of_nonneg_left hxLogScale hcPow.le
  have hmodulus :
      Real.log x ^ D <= ((eta / 4) * Real.log x) ^ (D + 1) := by
    calc
      Real.log x ^ D = Real.log x ^ D * 1 := by ring
      _ <= Real.log x ^ D *
          ((eta / 4) ^ (D + 1) * Real.log x) :=
        mul_le_mul_of_nonneg_left hscale (pow_nonneg hlogNonneg _)
      _ = ((eta / 4) * Real.log x) ^ (D + 1) := by
        rw [mul_pow, pow_succ]
        ring
  exact ⟨hx4, hxPNT, hmodulus, hxExp, hxFive, hxA⟩

private theorem majorArcRegionResidueWeightSum_sub_average_eq_projected
    {X k q r : Nat} (a : Fin k -> Real) (delta eta : Real)
    (hX : 1 < X) :
    majorArcResidueWeightSum (Finset.range X)
          (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
          q r -
        majorArcRegionTotalWeight X a delta eta /
          (q.totient : Complex) =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          ((majorArcLastPrimeProductResidueLogSum
              X a delta eta m q r : Complex) -
            (majorArcLastPrimeProductResidueLogSum
              X a delta eta m 1 0 : Complex) /
                (q.totient : Complex)) := by
  have htotal : majorArcRegionTotalWeight X a delta eta =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          (majorArcLastPrimeProductResidueLogSum
            X a delta eta m 1 0 : Complex) := by
    calc
      majorArcRegionTotalWeight X a delta eta =
          majorArcResidueWeightSum (Finset.range X)
            (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
            1 0 := by
          rw [majorArcResidueWeightSum_one_zero]
          rfl
      _ = _ := majorArcRegionResidueWeightSum_eq_projected a delta eta hX
  rw [majorArcRegionResidueWeightSum_eq_projected a delta eta hX, htotal]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem centered_four_error
    {aqU aqL a1U a1L U L phi E : Real}
    (hphi : 1 <= phi) (hE : 0 <= E)
    (hqU : abs (aqU - U / phi) <= E)
    (hqL : abs (aqL - L / phi) <= E)
    (h1U : abs (a1U - U) <= E)
    (h1L : abs (a1L - L) <= E) :
    abs ((aqU - aqL) - (a1U - a1L) / phi) <= 4 * E := by
  have hphiPos : 0 < phi := zero_lt_one.trans_le hphi
  have h1Udiv : abs ((a1U - U) / phi) <= E := by
    rw [abs_div, abs_of_pos hphiPos]
    exact (div_le_div₀ hE h1U zero_lt_one hphi).trans_eq (div_one E)
  have h1Ldiv : abs ((a1L - L) / phi) <= E := by
    rw [abs_div, abs_of_pos hphiPos]
    exact (div_le_div₀ hE h1L zero_lt_one hphi).trans_eq (div_one E)
  have halgebra :
      (aqU - aqL) - (a1U - a1L) / phi =
        (aqU - U / phi) - (aqL - L / phi) -
          (a1U - U) / phi + (a1L - L) / phi := by
    ring
  rw [halgebra]
  have habsSub (x y : Real) : abs (x - y) <= abs x + abs y := by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  calc
    _ <= abs ((aqU - U / phi) - (aqL - L / phi) -
        (a1U - U) / phi) + abs ((a1L - L) / phi) := abs_add_le _ _
    _ <= (abs ((aqU - U / phi) - (aqL - L / phi)) +
        abs ((a1U - U) / phi)) + abs ((a1L - L) / phi) := by
      gcongr
      exact habsSub _ _
    _ <= ((abs (aqU - U / phi) + abs (aqL - L / phi)) +
        abs ((a1U - U) / phi)) + abs ((a1L - L) / phi) := by
      gcongr
      exact habsSub _ _
    _ <= E + E + E + E := by gcongr
    _ = 4 * E := by ring

private theorem norm_majorArcLastPrimeProductResidueLogSum_sub_average_le
    {X K k m q r H B : Nat} {a : Fin k -> Real}
    {delta eta C x0 c ell : Real}
    (hC : 0 < C) (hx0 : 4 <= x0)
    (hPNT : ∀ x : Real, x0 <= x ->
      ∀ q : Nat, 0 < q -> IsDecimalSmooth q ->
        ∀ b : Nat, Nat.Coprime b q ->
          (q : Real) <= Real.log x ^ B ->
          abs (primeLogProgressionSum q b x -
            x / (q.totient : Real)) <=
              C * x / Real.log x ^ H)
    (hX : 1 < X) (heta : 0 < eta)
    (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hroom : ((k + 1 : Nat) : Real) <= 2 / eta)
    (hdelta0 : 0 <= delta) (hdelta : delta <= eta ^ 2 / 12)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X)
    (hm : 0 < m) (hq : 0 < q) (hr : Nat.Coprime r q)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0)
    (hc : 0 < c) (hell : 0 < ell)
    (hx0U : x0 <= (X : Real) / (m : Real))
    (hx0L : x0 <= majorArcLastPrimeLowerCutoff X a delta eta)
    (hqU : (q : Real) <=
      Real.log ((X : Real) / (m : Real)) ^ B)
    (hqL : (q : Real) <=
      Real.log (majorArcLastPrimeLowerCutoff X a delta eta) ^ B)
    (hlogU : c * ell <= Real.log ((X : Real) / (m : Real)))
    (hlogL : c * ell <=
      Real.log (majorArcLastPrimeLowerCutoff X a delta eta)) :
    ‖(majorArcLastPrimeProductResidueLogSum X a delta eta m q r : Complex) -
      (majorArcLastPrimeProductResidueLogSum X a delta eta m 1 0 : Complex) /
        (q.totient : Complex)‖ <=
      4 * C / c ^ H * ((X : Real) / (m : Real)) / ell ^ H := by
  let U : Real := (X : Real) / (m : Real)
  let L : Real := majorArcLastPrimeLowerCutoff X a delta eta
  let b := majorArcPrefixInverseResidue q m r
  let phi : Real := q.totient
  let E : Real := C * U / (c * ell) ^ H
  have hmq : Nat.Coprime m q :=
    projectedPrimeBoxWeightAtProduct_coprime_of_dvd_powerTen
      hX heta ha hlarge hpower hqdiv hweight
  have hb : Nat.Coprime b q := by
    dsimp [b]
    exact prefixInverseResidue_coprime hq hmq hr
  have hLU : L <= U := by
    dsimp [L, U]
    exact majorArcLastPrimeLowerCutoff_le_div_of_projectedWeight
      hX heta hsum hroom hdelta0 hdelta hm hweight
  have hSmooth : IsDecimalSmooth q :=
    (isDecimalSmooth_iff_exists_dvd_pow_ten q).2 ⟨K, by
      simpa [← hpower] using hqdiv⟩
  have hSmoothOne : IsDecimalSmooth 1 :=
    (isDecimalSmooth_iff_exists_dvd_pow_ten 1).2 ⟨0, by simp⟩
  have hqOne : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hOneU : (1 : Real) <= Real.log U ^ B :=
    hqOne.trans (by simpa [U] using hqU)
  have hOneL : (1 : Real) <= Real.log L ^ B :=
    hqOne.trans (by simpa [L] using hqL)
  have hpntqU := hPNT U (by simpa [U] using hx0U)
    q hq hSmooth b hb (by simpa [U] using hqU)
  have hpntqL := hPNT L (by simpa [L] using hx0L)
    q hq hSmooth b hb (by simpa [L] using hqL)
  have hpnt1U := hPNT U (by simpa [U] using hx0U)
    1 (by norm_num) hSmoothOne 0 (by simp) (by simpa using hOneU)
  have hpnt1L := hPNT L (by simpa [L] using hx0L)
    1 (by norm_num) hSmoothOne 0 (by simp) (by simpa using hOneL)
  have hcell : 0 < c * ell := mul_pos hc hell
  have hUFour : 4 <= U := hx0.trans (by simpa [U] using hx0U)
  have hLFour : 4 <= L := hx0.trans (by simpa [L] using hx0L)
  have hU0 : 0 <= U := by linarith
  have hL0 : 0 <= L := by linarith
  have hlogUpow : (c * ell) ^ H <= Real.log U ^ H :=
    pow_le_pow_left₀ hcell.le (by simpa [U] using hlogU) H
  have hlogLpow : (c * ell) ^ H <= Real.log L ^ H :=
    pow_le_pow_left₀ hcell.le (by simpa [L] using hlogL) H
  have hscale {y : Real} (hy0 : 0 <= y) (hyU : y <= U)
      (hlogpow : (c * ell) ^ H <= Real.log y ^ H) :
      C * y / Real.log y ^ H <= E := by
    have hden : 0 < (c * ell) ^ H := pow_pos hcell H
    calc
      C * y / Real.log y ^ H <= C * y / (c * ell) ^ H :=
        div_le_div_of_nonneg_left (mul_nonneg hC.le hy0) hden hlogpow
      _ <= C * U / (c * ell) ^ H :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hyU hC.le) hden.le
      _ = E := rfl
  have hqUscaled :
      abs (primeLogProgressionSum q b U - U / phi) <= E :=
    hpntqU.trans (hscale hU0 le_rfl hlogUpow)
  have hqLscaled :
      abs (primeLogProgressionSum q b L - L / phi) <= E :=
    hpntqL.trans (hscale hL0 hLU hlogLpow)
  have h1Uscaled : abs (primeLogProgressionSum 1 0 U - U) <= E := by
    simpa using hpnt1U.trans (hscale hU0 le_rfl hlogUpow)
  have h1Lscaled : abs (primeLogProgressionSum 1 0 L - L) <= E := by
    simpa using hpnt1L.trans (hscale hL0 hLU hlogLpow)
  have hphiNat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hphi : (1 : Real) <= phi := by
    dsimp [phi]
    exact_mod_cast hphiNat
  have hE : 0 <= E := by dsimp [E]; positivity
  have hcentered := centered_four_error hphi hE
    hqUscaled hqLscaled h1Uscaled h1Lscaled
  have hAq := majorArcLastPrimeProductResidueLogSum_eq_prefix_sub
    (a := a) (delta := delta) (eta := eta) (r := r) hm hq hmq hLU
  have hA1 := majorArcLastPrimeProductResidueLogSum_eq_prefix_sub
    (a := a) (delta := delta) (eta := eta) hm (by norm_num)
      (by simp) hLU (q := 1) (r := 0)
  have hbOne : majorArcPrefixInverseResidue 1 m 0 = 0 := by
    simp [majorArcPrefixInverseResidue]
  rw [hAq, hA1, hbOne]
  have hcast :
      ((primeLogProgressionSum q b U -
          primeLogProgressionSum q b L : Real) : Complex) -
          ((primeLogProgressionSum 1 0 U -
            primeLogProgressionSum 1 0 L : Real) : Complex) /
            (q.totient : Complex) =
        (((primeLogProgressionSum q b U - primeLogProgressionSum q b L) -
          (primeLogProgressionSum 1 0 U - primeLogProgressionSum 1 0 L) /
            (q.totient : Real) : Real) : Complex) := by
    push_cast
    rfl
  rw [show majorArcPrefixInverseResidue q m r = b by rfl]
  rw [show (X : Real) / (m : Real) = U by rfl]
  rw [show majorArcLastPrimeLowerCutoff X a delta eta = L by rfl]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  apply hcentered.trans_eq
  dsimp [E]
  rw [mul_pow]
  have hcH : 0 < c ^ H := pow_pos hc H
  have hellH : 0 < ell ^ H := pow_pos hell H
  field_simp

private theorem norm_sum_projectedPrimeBoxWeight_mul_le
    {X k R H : Nat} {a : Fin k -> Real} {delta G : Real}
    (hX : 4 <= X) (hk : k <= R) (hRH : R <= H) (hG : 0 <= G)
    (F : Nat -> Complex)
    (hF : ∀ m ∈ Finset.Ico 1 X,
      projectedPrimeBoxWeightAtProduct X a delta m ≠ 0 ->
      ‖F m‖ <= G * ((X : Real) / (m : Real)) /
        Real.log (X : Real) ^ H) :
    ‖∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) * F m‖ <=
      G * (2 * Real.log 4) ^ R * (X : Real) /
        Real.log (X : Real) ^ (H - R) := by
  let W := fun m => projectedPrimeBoxWeightAtProduct X a delta m
  let L := Real.log (X : Real)
  let C0 := 2 * Real.log 4
  have hL : 1 < L := by
    dsimp [L]
    have hXpos : (0 : Real) < X := by positivity
    exact (Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= X by omega))
  have hC0 : 1 <= C0 := by
    dsimp [C0]
    have : (1 : Real) < Real.log 4 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (Real.exp_one_lt_three.trans_le (by norm_num))
    linarith
  have hCoefficient : 0 <= G * (X : Real) / L ^ H := by positivity
  have hterm (m : Nat) (hm : m ∈ Finset.Ico 1 X) :
      ‖(W m : Complex) * F m‖ <=
        (G * (X : Real) / L ^ H) * (W m / (m : Real)) := by
    have hW : 0 <= W m :=
      projectedPrimeBoxWeightAtProduct_nonneg X a delta m
    by_cases hW0 : W m = 0
    · simp [hW0]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
      calc
        W m * ‖F m‖ <= W m *
            (G * ((X : Real) / (m : Real)) / L ^ H) :=
          mul_le_mul_of_nonneg_left
            (by simpa [L, W] using hF m hm hW0) hW
        _ = (G * (X : Real) / L ^ H) * (W m / (m : Real)) := by
          ring
  have hsubset : Finset.Ico 1 X ⊆ Finset.range X := by
    intro m hm
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
  have hharmonic :
      (∑ m ∈ Finset.Ico 1 X, W m / (m : Real)) <= (C0 * L) ^ k := by
    calc
      (∑ m ∈ Finset.Ico 1 X, W m / (m : Real)) <=
          ∑ m ∈ Finset.range X, W m / (m : Real) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro m hm hnot
        exact div_nonneg
          (projectedPrimeBoxWeightAtProduct_nonneg X a delta m)
          (by positivity)
      _ <= (C0 * L) ^ k := by
        simpa [C0, L, W] using
          sum_projectedPrimeBoxWeight_div_le_log_pow X a delta (by omega)
  have hbase : 1 <= C0 * L := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= C0 * L :=
        mul_le_mul hC0 hL.le zero_le_one (zero_le_one.trans hC0)
  have harity : (C0 * L) ^ k <= (C0 * L) ^ R :=
    pow_le_pow_right₀ hbase hk
  calc
    ‖∑ m ∈ Finset.Ico 1 X, (W m : Complex) * F m‖ <=
        ∑ m ∈ Finset.Ico 1 X, ‖(W m : Complex) * F m‖ :=
      norm_sum_le _ _
    _ <= ∑ m ∈ Finset.Ico 1 X,
        (G * (X : Real) / L ^ H) * (W m / (m : Real)) := by
      exact Finset.sum_le_sum fun m hm => hterm m hm
    _ = (G * (X : Real) / L ^ H) *
        ∑ m ∈ Finset.Ico 1 X, W m / (m : Real) := by
      rw [Finset.mul_sum]
    _ <= (G * (X : Real) / L ^ H) * (C0 * L) ^ k :=
      mul_le_mul_of_nonneg_left hharmonic hCoefficient
    _ <= (G * (X : Real) / L ^ H) * (C0 * L) ^ R :=
      mul_le_mul_of_nonneg_left harity hCoefficient
    _ = G * C0 ^ R * (X : Real) / L ^ (H - R) := by
      rw [mul_pow]
      have hLne : L ≠ 0 := ne_of_gt (zero_lt_one.trans hL)
      field_simp
      calc
        G * L ^ R * L ^ (H - R) = G * (L ^ (H - R) * L ^ R) := by
          ring
        _ = G * L ^ H := by rw [pow_sub_mul_pow L hRH]
    _ = _ := by rfl

/-- Every reduced residue receives its expected share of one complete source
region, uniformly at the logarithmic major-arc scale. -/
theorem exists_majorArcRegionResidueWeightSum_logScaleThreshold
    (D R : Nat) {eta : Real} (heta : 0 < eta) :
    ∃ X0 : Nat, ∀ X K k : Nat, X0 <= X -> k <= R ->
      ∀ a : Fin k -> Real, (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      X = 10 ^ K ->
      ∀ q : Nat, 0 < q -> q ∣ X ->
      (q : Real) <= Real.log (X : Real) ^ D ->
      ∀ r : Nat, Nat.Coprime r q ->
      ‖majorArcResidueWeightSum (Finset.range X)
          (fun n => (majorArcRegionWeightAtProduct X a
            (majorArcM2LogLogDelta X) eta n : Complex)) q r -
        majorArcRegionTotalWeight X a (majorArcM2LogLogDelta X) eta /
          (q.totient : Complex)‖ <=
        (X : Real) / Real.log (X : Real) ^ (4 * D) := by
  let H : Nat := 4 * D + R + 1
  let c : Real := eta / 4
  obtain ⟨C, xPNT, hC, hxPNT, hPNT⟩ :=
    exists_abs_primeLogProgressionSum_sub_main_log_pow_le H (D + 1)
  have hscalar := eventually_majorArcM3ScalarBounds D R heta C xPNT
  rcases eventually_atTop.mp hscalar with ⟨M, hM⟩
  let X0 := Nat.ceil (max M 4)
  refine ⟨X0, ?_⟩
  intro X K k hX0 hk a ha hsum hroom hpower q hq hqdiv hqLog r hr
  have hMX0 : M <= (X0 : Real) :=
    (le_max_left M 4).trans (Nat.le_ceil (max M 4))
  have hX0X : (X0 : Real) <= X := by exact_mod_cast hX0
  rcases hM (X : Real) (hMX0.trans hX0X) with
    ⟨hX4Real, hxPNTScale, hmodulus, hloglog, hlarge, habsorb⟩
  have hX4 : 4 <= X := by exact_mod_cast hX4Real
  have hX : 1 < X := by omega
  have hxPos : (0 : Real) < X := by positivity
  have hxNonneg : (0 : Real) <= X := hxPos.le
  have hell : 0 < Real.log (X : Real) := log_pos_of_four_le hX4Real
  have hc : 0 < c := by dsimp [c]; positivity
  have hloglog' : 12 / eta ^ 2 <= Real.log (Real.log (X : Real)) :=
    twelve_div_eta_sq_le_log_log_of_exp_exp_le hloglog
  have hdelta0 : 0 <= majorArcM2LogLogDelta X := by
    unfold majorArcM2LogLogDelta
    exact inv_nonneg.mpr
      ((show (0 : Real) <= 12 / eta ^ 2 by positivity).trans hloglog')
  have hdelta : majorArcM2LogLogDelta X <= eta ^ 2 / 12 := by
    unfold majorArcM2LogLogDelta
    exact inv_log_log_le_eta_sq_div_twelve heta hloglog'
  rw [majorArcRegionResidueWeightSum_sub_average_eq_projected
    a (majorArcM2LogLogDelta X) eta hX]
  let F : Nat -> Complex := fun m =>
    (majorArcLastPrimeProductResidueLogSum X a
      (majorArcM2LogLogDelta X) eta m q r : Complex) -
      (majorArcLastPrimeProductResidueLogSum X a
        (majorArcM2LogLogDelta X) eta m 1 0 : Complex) /
          (q.totient : Complex)
  let G : Real := 4 * C / c ^ H
  have hG : 0 <= G := by dsimp [G]; positivity
  have hsumBound := norm_sum_projectedPrimeBoxWeight_mul_le
    (a := a) (delta := majorArcM2LogLogDelta X) (G := G)
    hX4 hk (show R <= H by dsimp [H]; omega) hG F
  refine (hsumBound ?_).trans ?_
  · intro m hm hweight
    have hmPos : 0 < m := (Finset.mem_Ico.mp hm).1
    let L := majorArcLastPrimeLowerCutoff X a
      (majorArcM2LogLogDelta X) eta
    let U : Real := (X : Real) / (m : Real)
    have hLU : L <= U := by
      dsimp [L, U]
      exact majorArcLastPrimeLowerCutoff_le_div_of_projectedWeight
        hX heta hsum hroom hdelta0 hdelta hmPos hweight
    have hpowerLower : (X : Real) ^ c <= L := by
      dsimp [L, c, majorArcLastPrimeLowerCutoff]
      exact le_max_left _ _
    have hpowerUpper : (X : Real) ^ c <= U := hpowerLower.trans hLU
    have hlogLower : c * Real.log (X : Real) <= Real.log L := by
      rw [← Real.log_rpow hxPos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hxPos _) hpowerLower
    have hlogUpper : c * Real.log (X : Real) <= Real.log U := by
      rw [← Real.log_rpow hxPos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hxPos _) hpowerUpper
    have hpLower := pow_le_pow_left₀ (mul_pos hc hell).le hlogLower (D + 1)
    have hpUpper := pow_le_pow_left₀ (mul_pos hc hell).le hlogUpper (D + 1)
    apply norm_majorArcLastPrimeProductResidueLogSum_sub_average_le
      hC hxPNT hPNT hX heta ha hsum hroom hdelta0 hdelta hlarge
      hpower hqdiv hmPos hq hr hweight hc hell
    · exact hxPNTScale.trans hpowerUpper
    · exact hxPNTScale.trans hpowerLower
    · exact hqLog.trans (hmodulus.trans hpUpper)
    · exact hqLog.trans (hmodulus.trans hpLower)
    · exact hlogUpper
    · exact hlogLower
  · dsimp [G, H, c] at habsorb ⊢
    have hden : 0 < Real.log (X : Real) ^ (4 * D + 1) :=
      pow_pos hell _
    calc
      4 * C / (eta / 4) ^ (4 * D + R + 1) *
            (2 * Real.log 4) ^ R * (X : Real) /
          Real.log (X : Real) ^ (4 * D + R + 1 - R) =
        (4 * C / (eta / 4) ^ (4 * D + R + 1) *
            (2 * Real.log 4) ^ R) * (X : Real) /
          Real.log (X : Real) ^ (4 * D + 1) := by
            rw [show 4 * D + R + 1 - R = 4 * D + 1 by omega]
      _ <= Real.log (X : Real) * (X : Real) /
          Real.log (X : Real) ^ (4 * D + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right habsorb hxNonneg) hden.le
      _ = (X : Real) / Real.log (X : Real) ^ (4 * D) := by
        rw [pow_succ']
        field_simp

end PrimesRestrictedDigits
