import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Fixed-strip Dirichlet Gamma-factor ratio

This file proves the absolute polynomial bound for the Gamma-factor quotient
used in the primitive functional equation. The source comparison is
Koukoulopoulos, printed p. 24, Exercise 1.12(a), and printed p. 114,
Lemma 11.4; see semantic review SEM-476.

The proof uses an eleven-step reciprocal-Gamma recurrence and Euler's Beta
integral. This retains Mathlib's totalized values at the classical Gamma
poles instead of imposing a nonzero denominator hypothesis.
-/

namespace BoundedGaps.Maynard

open Complex Set MeasureTheory

private lemma one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat
    (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ j ∈ Finset.range n, (z + j)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
        Finset.prod_range_succ, Nat.cast_succ]
      ring_nf

private lemma Gamma_div_Gamma_eq_prod_mul_beta_div
    (w X : ℂ) (d : ℝ) (hX : 0 < X.re) (hd : 0 < d)
    (hsum : X + (d : ℂ) = w + 11) :
    Complex.Gamma X / Complex.Gamma w =
      (∏ j ∈ Finset.range 11, (w + j)) *
        (Complex.betaIntegral X d / Complex.Gamma d) := by
  have hXd : 0 < (X + (d : ℂ)).re := by simp; linarith
  have hGXd := Complex.Gamma_ne_zero_of_re_pos hXd
  have hGd := Complex.Gamma_ne_zero_of_re_pos
    (show 0 < ((d : ℂ)).re by simpa)
  rw [div_eq_mul_inv, one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat w 11]
  have hsum' : w + (11 : ℕ) = X + (d : ℂ) := by simpa using hsum.symm
  rw [hsum', Complex.betaIntegral_eq_Gamma_mul_div X d hX
    (show 0 < ((d : ℂ)).re by simpa)]
  field_simp [hGXd, hGd]

private lemma norm_betaIntegral_fixed_re_le
    {u : ℂ} {q : ℝ} (hu : (1 / 4 : ℝ) ≤ u.re)
    (hq : (1 / 2 : ℝ) ≤ q) :
    ‖Complex.betaIntegral u q‖ ≤ 12 := by
  rw [Complex.betaIntegral]
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ ((q : ℂ) - 1)
  let g : ℝ → ℝ := fun x =>
    2 * x ^ (-(3 / 4 : ℝ)) + 2 * (1 - x) ^ (-(1 / 2 : ℝ))
  have hxpow : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hhalfpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hsubpow :
      IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hhalfpow.comp_sub_left 1).symm
  have hg : IntervalIntegrable g volume 0 1 :=
    (hxpow.const_mul 2).add (hsubpow.const_mul 2)
  have hf : IntervalIntegrable f volume 0 1 :=
    Complex.betaIntegral_convergent
      (lt_of_lt_of_le (by norm_num) hu)
      (show 0 < ((q : ℂ)).re by simp; linarith)
  have hpoint : ∀ x : ℝ, x ∈ Icc 0 1 → ‖f x‖ ≤ g x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · have hzero : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 1 := by
        by_cases h : u - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    rcases eq_or_ne x 1 with rfl | hx1
    · have hzero : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 1 := by
        by_cases h : (q : ℂ) - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hsubpos : 0 < 1 - x := sub_pos.mpr hxlt
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hsubpos]
    simp only [sub_re, one_re, ofReal_re]
    have hxpow_le : x ^ (u.re - 1) ≤ x ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by linarith)
    have hsubpow_le :
        (1 - x) ^ (q - 1) ≤ (1 - x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by linarith)
    have hxnonneg := Real.rpow_nonneg hxpos.le (u.re - 1)
    have hsubnonneg := Real.rpow_nonneg hsubpos.le (q - 1)
    have hbase :
        x ^ (u.re - 1) * (1 - x) ^ (q - 1) ≤
          x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul hxpow_le hsubpow_le hsubnonneg
        (Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ)))
    have hmajor :
        x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤ g x := by
      by_cases hhalf : x ≤ 1 / 2
      · have hsubhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
        have hone :
            (1 - x) ^ (-(1 / 2 : ℝ)) ≤ (1 - x) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by norm_num)
        have hinv : (1 - x) ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hsubpos (by norm_num)).2 hsubhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
      · have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_ge hhalf
        have hone :
            x ^ (-(3 / 4 : ℝ)) ≤ x ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by norm_num)
        have hinv : x ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hxpos (by norm_num)).2 hxhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
    exact hbase.trans hmajor
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, g x :=
      intervalIntegral.integral_mono_on (by norm_num) hf.norm hg hpoint
    _ = 12 := by
      dsimp [g]
      rw [intervalIntegral.integral_add (hxpow.const_mul 2) (hsubpow.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hsub :
          (∫ x in (0 : ℝ)..1, (1 - x) ^ (-(1 / 2 : ℝ))) =
            ∫ x in (0 : ℝ)..1, x ^ (-(1 / 2 : ℝ)) := by
        simpa using intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1
      rw [hsub, integral_rpow (Or.inl (by norm_num)),
        integral_rpow (Or.inl (by norm_num))]
      norm_num

private lemma exists_norm_one_div_Gamma_Icc_le :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K := by
  have hcont : Continuous (fun d : ℝ => ‖(Complex.Gamma (d : ℂ))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp
      Complex.continuous_ofReal).norm
  obtain ⟨c, hc⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont.continuousOn)
  let K : ℝ := max c 0 + 1
  refine ⟨K, by dsimp [K]; linarith [le_max_right c 0], ?_⟩
  intro d hd hd11
  have hdmem : d ∈ Icc (1 / 2 : ℝ) 11 := ⟨hd, hd11⟩
  exact (hc _ (mem_image_of_mem _ hdmem)).trans
    (by dsimp [K]; linarith [le_max_left c 0])

private lemma norm_prod_range_eleven_add_le
    (w : ℂ) (t : ℝ)
    (hwlower : -(5 : ℝ) ≤ w.re) (hwupper : w.re ≤ (3 / 4 : ℝ))
    (hwim : |w.im| = |t| / 2) :
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
      (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by
  have hfactor : ∀ j ∈ Finset.range 11,
      ‖w + (j : ℂ)‖ ≤ 6 * (|t| + 2) := by
    intro j hj
    have hjlt : j < 11 := Finset.mem_range.mp hj
    have hjle : j ≤ 10 := Nat.le_pred_of_lt hjlt
    have hjreal : (j : ℝ) ≤ 10 := by exact_mod_cast hjle
    have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hreabs : |(w + (j : ℂ)).re| ≤ 43 / 4 := by
      rw [add_re, natCast_re]
      apply abs_le.mpr
      constructor <;> linarith
    have himabs : |(w + (j : ℂ)).im| = |t| / 2 := by
      simp only [add_im, natCast_im, add_zero, hwim]
    calc
      ‖w + (j : ℂ)‖ ≤ |(w + (j : ℂ)).re| + |(w + (j : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 43 / 4 + |t| / 2 := by rw [himabs]; gcongr
      _ ≤ 6 * (|t| + 2) := by nlinarith [abs_nonneg t]
  calc
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
        ∏ j ∈ Finset.range 11, ‖w + (j : ℂ)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _j ∈ Finset.range 11, (6 * (|t| + 2)) := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfactor
    _ = (6 * (|t| + 2)) ^ 11 := by simp
    _ = (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by ring

private lemma norm_Gamma_div_Gamma_fixedStrip_le
    (K : ℝ)
    (hK : ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K)
    (a : ℝ) (s : ℂ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hslo : -(10 : ℝ) ≤ s.re) (hshi : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ ≤
      (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by
  let w : ℂ := ((starRingEnd ℂ) s + (a : ℂ)) / 2
  let X : ℂ := (1 - s + (a : ℂ)) / 2
  let d : ℝ := 21 / 2 + s.re
  have hwlower : -(5 : ℝ) ≤ w.re := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwupper : w.re ≤ (3 / 4 : ℝ) := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwim : |w.im| = |s.im| / 2 := by
    rw [show w.im = -s.im / 2 by norm_num [w], abs_div, abs_neg]
    norm_num
  have hX : (1 / 4 : ℝ) ≤ X.re := by
    rw [show X.re = (1 - s.re + a) / 2 by norm_num [X]]
    linarith
  have hdlo : (1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith
  have hdhi : d ≤ 11 := by dsimp [d]; linarith
  have hsum : X + (d : ℂ) = w + 11 := by
    dsimp [X, d, w]
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  have hidentity := Gamma_div_Gamma_eq_prod_mul_beta_div w X d
    (lt_of_lt_of_le (by norm_num) hX) (lt_of_lt_of_le (by norm_num) hdlo) hsum
  have hwconj : w = (starRingEnd ℂ) ((s + (a : ℂ)) / 2) := by
    dsimp [w]
    rw [map_div₀, map_add, map_ofNat]
    norm_num
  have hdennorm :
      ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖ = ‖Complex.Gamma w‖ := by
    have h := congrArg norm (Complex.Gamma_conj ((s + (a : ℂ)) / 2))
    rw [Complex.norm_conj] at h
    rw [hwconj, h]
  have hquotnorm :
      ‖Complex.Gamma X / Complex.Gamma ((s + (a : ℂ)) / 2)‖ =
        ‖Complex.Gamma X / Complex.Gamma w‖ := by
    simp only [norm_div, hdennorm]
  have hprod := norm_prod_range_eleven_add_le w s.im hwlower hwupper hwim
  have hresidual :
      ‖Complex.betaIntegral X d / Complex.Gamma d‖ ≤ 12 * K := by
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul (norm_betaIntegral_fixed_re_le hX hdlo)
      (hK d hdlo hdhi) (norm_nonneg _) (by norm_num)
  rw [show (1 - s + (a : ℂ)) / 2 = X by rfl, hquotnorm, hidentity, norm_mul]
  calc
    _ ≤ ((6 : ℝ) ^ 11 * (|s.im| + 2) ^ 11) * (12 * K) :=
      mul_le_mul hprod hresidual (norm_nonneg _)
        (mul_nonneg (by positivity) (by positivity))
    _ = (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by ring

private lemma norm_GammaR_div_GammaR_le_Gamma_div_Gamma
    (a : ℝ) (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
        Complex.Gammaℝ (s + (a : ℂ))‖ ≤
      ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hfactor :
      ((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2) *
          Complex.Gamma ((1 - s + (a : ℂ)) / 2)) /
        ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2) *
          Complex.Gamma ((s + (a : ℂ)) / 2)) =
      (((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2)) /
          ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2))) *
        (Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
          Complex.Gamma ((s + (a : ℂ)) / 2)) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hfactor, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_sub Real.pi_pos]
  have hexp :
      (-(1 - s + (a : ℂ)) / 2).re - (-(s + (a : ℂ)) / 2).re =
        s.re - 1 / 2 := by
    norm_num
    ring
  rw [hexp]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_trans (by norm_num) Real.two_le_pi) (by linarith)

private lemma even_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Even) :
    (chi⁻¹).Even := by
  simp only [DirichletCharacter.Even] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi, inv_one]

private lemma odd_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Odd) :
    (chi⁻¹).Odd := by
  simp only [DirichletCharacter.Odd] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi]
  norm_num

/-- The Dirichlet Gamma-factor quotient has absolute polynomial growth on
the fixed left strip used by the local zero-expansion argument.

The constant is uniform in the modulus and character. No nonzero hypothesis
is imposed on the denominator Gamma factor; this includes the parity-
dependent trivial-zero points under Lean's totalized division. -/
theorem exists_norm_gammaFactor_ratio_fixedStrip_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (s : ℂ),
        -(10 : ℝ) ≤ s.re →
        s.re ≤ (1 / 2 : ℝ) →
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ ≤
          C * (|s.im| + 2) ^ 11 := by
  obtain ⟨K, hKpos, hK⟩ := exists_norm_one_div_Gamma_Icc_le
  let C : ℝ := 12 * K * 6 ^ 11
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q _ chi s hslo hshi
  have hbound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
      ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
          Complex.Gammaℝ (s + (a : ℂ))‖ ≤
        C * (|s.im| + 2) ^ 11 := by
    exact (norm_GammaR_div_GammaR_le_Gamma_div_Gamma a s hshi).trans
      (norm_Gamma_div_Gamma_fixedStrip_le K hK a s ha0 ha1 hslo hshi)
  rcases chi.even_or_odd with heven | hodd
  · rw [(even_inv_for_gammaFactor heven).gammaFactor_def, heven.gammaFactor_def]
    simpa using hbound 0 (by norm_num) (by norm_num)
  · rw [(odd_inv_for_gammaFactor hodd).gammaFactor_def, hodd.gammaFactor_def]
    convert hbound 1 (by norm_num) (by norm_num) using 1
    all_goals norm_num

end BoundedGaps.Maynard
