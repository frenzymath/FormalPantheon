import BoundedGaps.Maynard.VolterraIncrement
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

noncomputable section

/-!
# Stability of the discrete Wirsing Volterra recurrence

This proves the explicit large-endpoint stability lemma below the corrected
`kappa = 1` Wirsing estimate in FordSieve2023, Theorem 4.4, pp. 47--51.
Ford supplies the source-scale motivation; the discrete monotone ratios and
constant seven are proved here directly.
-/

open scoped Topology
open Filter

namespace BoundedGaps.Maynard

private lemma volterraFactorLower {t E c a : ℝ}
    (hE : 0 < E) (hc : 0 ≤ c) (ha : 0 ≤ a) (hac : a ≤ c) (ht : 0 ≤ t) :
    ((t + a + E + c) / (t + E + c)) ^ 2 ≤
      1 + 2 * a / (t + E) := by
  have hden₁ : 0 < t + E := by linarith
  have hden₂ : 0 < t + E + c := by linarith
  have hden₂' : 0 < (t + E + c)^2 := sq_pos_of_pos hden₂
  field_simp [ne_of_gt hden₁, ne_of_gt hden₂]
  have hcore : 0 ≤ 2 * c * (t + E + c) - a * (t + E) := by
    have hmul : a * (t + E) ≤ c * (t + E) :=
      mul_le_mul_of_nonneg_right hac (by linarith)
    have hstep : c * (t + E) ≤ 2 * c * (t + E + c) := by
      nlinarith [mul_nonneg hc (by linarith : 0 ≤ t + E)]
    linarith
  have hprod := mul_nonneg ha hcore
  nlinarith [hprod]

private lemma volterraFactorUpper {t E F a : ℝ}
    (hEF : E ≤ F) (htF : F < t) (ha : 0 ≤ a) :
    1 + 2 * a / (t - E) ≤ ((t + a - F) / (t - F)) ^ 2 := by
  have hdenE : 0 < t - E := by linarith
  have hdenF : 0 < t - F := by linarith
  field_simp [ne_of_gt hdenE, ne_of_gt hdenF]
  have hprod : 0 ≤ a * (2 * (t - F) * (F - E) + (t - E) * a) := by
    apply mul_nonneg ha
    positivity
  nlinarith [hprod]

private lemma volterraCrossUpper {t E F a V X : ℝ}
    (hEF : E ≤ F) (htF : F < t) (ha : 0 ≤ a) (hV : 0 ≤ V)
    (hX : X ≤ V * (1 + 2 * a / (t - E))) :
    X * (t - F)^2 ≤ V * (t + a - F)^2 := by
  have hfac := volterraFactorUpper (t := t) (E := E) (F := F)
    hEF htF ha
  have hmul := mul_le_mul_of_nonneg_left hfac hV
  have hmain : X ≤ V * ((t + a - F) / (t - F))^2 := hX.trans hmul
  have hden : 0 < (t - F)^2 := sq_pos_of_pos (sub_pos.mpr htF)
  calc
    X * (t - F)^2 ≤
        (V * ((t + a - F) / (t - F))^2) * (t - F)^2 :=
      mul_le_mul_of_nonneg_right hmain (sq_nonneg _)
    _ = V * (t + a - F)^2 := by
      field_simp [ne_of_gt (sub_pos.mpr htF)]

theorem abstractVolterra_stability_large
    (M : ℕ → ℝ) (δ E : ℝ)
    (hδ : 0 < δ) (hE : 0 < E)
    (hMnonneg : ∀ n, 0 ≤ M n)
    (hbal : ∀ {n : ℕ}, 0 < n →
      |Real.log n * M n - 2 * abstractVolterraIncrement M n| ≤ E * M n)
    (hnorm : Tendsto (fun n : ℕ => M n / Real.log n) atTop (𝓝 δ)) :
    ∀ {n : ℕ}, 2 * (E + Real.log 2) ≤ Real.log n →
      |M n - δ * Real.log n| ≤ 7 * δ * (E + Real.log 2) := by
  let F : ℝ := E + Real.log 2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hF : 0 < F := by dsimp [F]; linarith
  have hVnonneg : ∀ n, 0 ≤ abstractVolterraIncrement M n := by
    intro n
    unfold abstractVolterraIncrement
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (log_increment_nonneg i) (hMnonneg i)
  have hVratio : Tendsto
      (fun n : ℕ => abstractVolterraIncrement M n / (Real.log n)^2)
      atTop (𝓝 (δ / 2)) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hlogpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n :=
      hlog.eventually (eventually_gt_atTop 0)
    have hratio := hnorm
    have hsmall : Tendsto (fun n : ℕ =>
        (E / Real.log n) * (M n / Real.log n)) atTop (𝓝 0) := by
      have hEinv : Tendsto (fun n : ℕ => E / Real.log n) atTop (𝓝 0) :=
        hlog.const_div_atTop E
      simpa using hEinv.mul hratio
    have hdiff : Tendsto (fun n : ℕ =>
        (Real.log n * M n - 2 * abstractVolterraIncrement M n) /
          (Real.log n)^2) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
        ?_ hsmall
      filter_upwards [hlogpos] with n hn
      rw [abs_div, abs_of_pos (sq_pos_of_pos hn)]
      have hb := hbal (n := n) (by exact Nat.pos_of_ne_zero (by
        intro hn0; simp [hn0] at hn))
      calc
        |Real.log n * M n - 2 * abstractVolterraIncrement M n| /
            (Real.log n)^2 ≤ (E * M n) / (Real.log n)^2 :=
          div_le_div_of_nonneg_right hb (sq_nonneg _)
        _ = (E / Real.log n) * (M n / Real.log n) := by
          field_simp
    have hrewrite : (fun n : ℕ =>
        (Real.log n * M n - 2 * abstractVolterraIncrement M n) /
          (Real.log n)^2) =ᶠ[atTop] (fun n : ℕ =>
        M n / Real.log n -
          2 * abstractVolterraIncrement M n / (Real.log n)^2) := by
      filter_upwards [hlogpos] with n hn
      field_simp
    have hdiff' : Tendsto (fun n : ℕ =>
        M n / Real.log n -
          2 * abstractVolterraIncrement M n / (Real.log n)^2)
        atTop (𝓝 0) := hdiff.congr' hrewrite
    have hVtwo : Tendsto (fun n : ℕ =>
        2 * abstractVolterraIncrement M n / (Real.log n)^2)
        atTop (𝓝 δ) := by
      have := (hnorm.sub hdiff')
      simpa [sub_eq_add_neg] using this
    exact (hVtwo.div_const 2).congr'
      (Filter.Eventually.of_forall (fun n => by ring))
  have hplusRatio : Tendsto (fun n : ℕ =>
      abstractVolterraIncrement M n / (Real.log n + F)^2)
      atTop (𝓝 (δ / 2)) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hFdiv : Tendsto (fun n : ℕ => F / Real.log n) atTop (𝓝 0) :=
      hlog.const_div_atTop F
    have hden : Tendsto (fun n : ℕ =>
        (Real.log n + F)^2 / (Real.log n)^2) atTop (𝓝 1) := by
      have hpow : Tendsto (fun n : ℕ => (1 + F / Real.log n)^2)
          atTop (𝓝 ((1 + 0)^2)) :=
        (tendsto_const_nhds.add hFdiv).pow 2
      have hpow' : Tendsto (fun n : ℕ => (1 + F / Real.log n)^2)
          atTop (𝓝 1) := by simpa using hpow
      refine hpow'.congr' ?_
      filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with n hn
      field_simp
    have hquot := hVratio.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hquot' : Tendsto
        (fun n : ℕ =>
          (abstractVolterraIncrement M n / (Real.log n)^2) /
            ((Real.log n + F)^2 / (Real.log n)^2))
        atTop (𝓝 ((δ / 2) / 1)) := hquot
    have heq : (fun n : ℕ =>
          (abstractVolterraIncrement M n / (Real.log n)^2) /
            ((Real.log n + F)^2 / (Real.log n)^2)) =ᶠ[atTop]
        (fun n : ℕ =>
          abstractVolterraIncrement M n / (Real.log n + F)^2) := by
      filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
      have hnF : Real.log n + F ≠ 0 := ne_of_gt (by linarith)
      field_simp
    simpa using hquot'.congr' heq
  have hminusRatio : Tendsto (fun n : ℕ =>
      abstractVolterraIncrement M n / (Real.log n - F)^2)
      atTop (𝓝 (δ / 2)) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hFdiv : Tendsto (fun n : ℕ => F / Real.log n) atTop (𝓝 0) :=
      hlog.const_div_atTop F
    have hden : Tendsto (fun n : ℕ =>
        (Real.log n - F)^2 / (Real.log n)^2) atTop (𝓝 1) := by
      have hpow : Tendsto (fun n : ℕ => (1 - F / Real.log n)^2)
          atTop (𝓝 ((1 - 0)^2)) :=
        (tendsto_const_nhds.sub hFdiv).pow 2
      have hpow' : Tendsto (fun n : ℕ => (1 - F / Real.log n)^2)
          atTop (𝓝 1) := by simpa using hpow
      refine hpow'.congr' ?_
      filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with n hn
      field_simp
    have hquot := hVratio.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hquot' : Tendsto
        (fun n : ℕ =>
          (abstractVolterraIncrement M n / (Real.log n)^2) /
            ((Real.log n - F)^2 / (Real.log n)^2))
        atTop (𝓝 ((δ / 2) / 1)) := hquot
    have heq : (fun n : ℕ =>
          (abstractVolterraIncrement M n / (Real.log n)^2) /
            ((Real.log n - F)^2 / (Real.log n)^2)) =ᶠ[atTop]
        (fun n : ℕ =>
          abstractVolterraIncrement M n / (Real.log n - F)^2) := by
      filter_upwards [hlog.eventually (eventually_gt_atTop F)] with n hn
      have hn0 : Real.log n ≠ 0 := ne_of_gt (hF.trans hn)
      have hnF : Real.log n - F ≠ 0 := ne_of_gt (sub_pos.mpr hn)
      field_simp
    simpa using hquot'.congr' heq
  let V : ℕ → ℝ := abstractVolterraIncrement M
  let Hp : ℕ → ℝ := fun n => V n / (Real.log n + F)^2
  have hHp_step : ∀ n : ℕ, Hp n ≤ Hp (n + 1) := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [Hp, V, abstractVolterraIncrement]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have ht : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have ha : 0 ≤ Real.log (n + 1) - Real.log n :=
        log_increment_nonneg n
      have hac : Real.log (n + 1) - Real.log n ≤ Real.log 2 :=
        log_increment_le_log_two hnpos
      have hbaln := hbal (n := n) hnpos
      have hupper : 2 * V n ≤ (Real.log n + E) * M n := by
        have hh := (abs_le.mp (by simpa [V] using hbaln)).1
        change 2 * abstractVolterraIncrement M n ≤
          (Real.log n + E) * M n
        nlinarith [hh]
      have hdenE : 0 < Real.log n + E := by linarith
      have hlower : (Real.log n - E) * M n ≤
          2 * abstractVolterraIncrement M n := by
        have hh := (abs_le.mp (by simpa [V] using hbaln)).2
        linarith
      have hMlower : 2 * V n / (Real.log n + E) ≤ M n :=
        (div_le_iff₀ hdenE).2 (by simpa [mul_comm] using hupper)
      have hfac := volterraFactorLower (t := Real.log n) (E := E)
        (c := Real.log 2) (a := Real.log (n + 1) - Real.log n)
        hE hlog2 ha hac ht
      have hstep : V n *
          ((Real.log n + (Real.log (n + 1) - Real.log n) + E + Real.log 2) /
            (Real.log n + E + Real.log 2)) ^ 2 ≤
          V n + (Real.log (n + 1) - Real.log n) * M n := by
        have hfac' := mul_le_mul_of_nonneg_left hfac
          (by simpa [V] using hVnonneg n)
        have hfac'' : V n *
            (1 + 2 * (Real.log (n + 1) - Real.log n) /
              (Real.log n + E)) ≤
            V n + (Real.log (n + 1) - Real.log n) * M n := by
          calc
            V n * (1 + 2 * (Real.log (n + 1) - Real.log n) /
                (Real.log n + E)) =
                V n + (Real.log (n + 1) - Real.log n) *
                  (2 * V n / (Real.log n + E)) := by
                    field_simp
            _ ≤ V n + (Real.log (n + 1) - Real.log n) * M n := by
              gcongr
        exact hfac'.trans hfac''
      have hden : 0 < (Real.log n + F)^2 := by
        exact sq_pos_of_pos (by linarith)
      have hcross : V n *
          (Real.log (n + 1) + F)^2 ≤
          (V n + (Real.log (n + 1) - Real.log n) * M n) *
            (Real.log n + F)^2 := by
        have hstep' := hstep
        have hlogsucc : Real.log (n + 1) =
            Real.log n + (Real.log (n + 1) - Real.log n) := by ring
        field_simp [ne_of_gt (by linarith :
          0 < Real.log n + E + Real.log 2),
          ne_of_gt (by linarith : 0 < Real.log n + E)] at hstep'
        rw [hlogsucc]
        dsimp [F]
        convert hstep' using 1 <;> ring_nf
      dsimp [Hp, V]
      rw [abstractVolterraIncrement_succ]
      have hposNext : 0 < Real.log (↑(n + 1)) + F := by
        have htNext : 0 ≤ Real.log (↑(n + 1)) :=
          Real.log_natCast_nonneg _
        linarith
      exact (div_le_div_iff₀ hden
        (sq_pos_of_pos hposNext)).2 (by simpa [V] using hcross)
  have hHp_mono : Monotone Hp := by
    exact monotone_nat_of_le_succ hHp_step
  have hHp_bound : ∀ n : ℕ, Hp n ≤ δ / 2 := by
    intro n
    apply ge_of_tendsto (by simpa [Hp, V] using hplusRatio)
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact hHp_mono hnm
  let Hm : ℕ → ℝ := fun n =>
    V n / (Real.log n - F)^2
  have hminusRatio : Tendsto (fun n : ℕ =>
      V n / (Real.log n - F)^2)
      atTop (𝓝 (δ / 2)) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hFdiv : Tendsto (fun n : ℕ => F / Real.log n) atTop (𝓝 0) :=
      hlog.const_div_atTop F
    have hden : Tendsto (fun n : ℕ =>
        (Real.log n - F)^2 / (Real.log n)^2) atTop (𝓝 1) := by
      have hpow : Tendsto (fun n : ℕ => (1 - F / Real.log n)^2)
          atTop (𝓝 ((1 - 0)^2)) :=
        (tendsto_const_nhds.sub hFdiv).pow 2
      have hpow' : Tendsto (fun n : ℕ => (1 - F / Real.log n)^2)
          atTop (𝓝 1) := by simpa using hpow
      refine hpow'.congr' ?_
      filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with n hn
      field_simp
    have hquot := hVratio.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun n : ℕ =>
          (V n / (Real.log n)^2) /
            ((Real.log n - F)^2 / (Real.log n)^2)) =ᶠ[atTop]
        (fun n : ℕ => V n / (Real.log n - F)^2) := by
      filter_upwards [hlog.eventually (eventually_gt_atTop F)] with n hn
      have hnlog : 0 < Real.log n := hF.trans hn
      have hnF : Real.log n - F ≠ 0 := ne_of_gt (sub_pos.mpr hn)
      field_simp [ne_of_gt hnlog, hnF]
    simpa [Hm] using hquot.congr' heq
  have hHm_step : ∀ {n : ℕ}, F < Real.log n → Hm (n + 1) ≤ Hm n := by
    intro n hnF
    have hnpos : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
      have : F < 0 := by simpa [hnzero] using hnF
      linarith
    have ht : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have ha : 0 ≤ Real.log (n + 1) - Real.log n :=
      log_increment_nonneg n
    have hEF : E ≤ F := by dsimp [F]; linarith [hlog2]
    have hfac := volterraFactorUpper (t := Real.log n) (E := E) (F := F)
      (a := Real.log (n + 1) - Real.log n) hEF hnF ha
    have hbaln := hbal (n := n) hnpos
    have hlower : (Real.log n - E) * M n ≤ 2 * V n := by
      have hh := (abs_le.mp (by simpa [V] using hbaln)).2
      change (Real.log n - E) * M n ≤
        2 * abstractVolterraIncrement M n
      nlinarith [hh]
    have hdenE : 0 < Real.log n - E := by
      have : E ≤ F := by dsimp [F]; linarith [hlog2]
      linarith
    have hMupper : M n ≤ 2 * V n / (Real.log n - E) :=
      (le_div_iff₀ hdenE).2 (by simpa [mul_comm] using hlower)
    have hstep : V n +
        (Real.log (n + 1) - Real.log n) * M n ≤
        V n * (1 + 2 * (Real.log (n + 1) - Real.log n) /
          (Real.log n - E)) := by
      have hmul := mul_le_mul_of_nonneg_left hMupper ha
      calc
        V n + (Real.log (n + 1) - Real.log n) * M n ≤
            V n + (Real.log (n + 1) - Real.log n) *
              (2 * V n / (Real.log n - E)) := by gcongr
        _ = V n * (1 + 2 * (Real.log (n + 1) - Real.log n) /
            (Real.log n - E)) := by field_simp
    have hfac' := mul_le_mul_of_nonneg_left hfac (hVnonneg n)
    have hcross' :
        (V n + (Real.log (n + 1) - Real.log n) * M n) *
            (Real.log n - F)^2 ≤
          V n * (Real.log (n + 1) - F)^2 := by
      have hc := volterraCrossUpper (t := Real.log n) (E := E) (F := F)
        (a := Real.log (n + 1) - Real.log n) (V := V n)
        (X := V n + (Real.log (n + 1) - Real.log n) * M n)
        hEF hnF ha (by simpa [V] using hVnonneg n) hstep
      convert hc using 1
      all_goals ring_nf
    have hstep' :
      (V n + (Real.log (n + 1) - Real.log n) * M n) /
        (Real.log (n + 1) - F)^2 ≤
      V n / (Real.log n - F)^2 := by
      have hdenOld : 0 < (Real.log n - F)^2 :=
        sq_pos_of_pos (sub_pos.mpr hnF)
      have hdenNext : 0 < (Real.log (n + 1) - F)^2 := by
        have htNext : 0 ≤ Real.log (n + 1) := by
          apply Real.log_nonneg
          norm_num
        exact sq_pos_of_pos (by linarith)
      exact (div_le_div_iff₀ hdenNext hdenOld).2 hcross'
    dsimp [Hm, V]
    rw [abstractVolterraIncrement_succ]
    simpa [V, Nat.cast_add, Nat.cast_one] using hstep'
  have hHm_tail : ∀ {n m : ℕ}, F < Real.log n → n ≤ m → Hm m ≤ Hm n := by
    intro n m hn hnm
    induction hnm with
    | refl => exact le_rfl
    | @step m hnm ih =>
      exact (hHm_step (n := m) (by
        have hlogmono : Real.log n ≤ Real.log m := by
          have hnpos : 0 < n := by
            by_contra hn0
            have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
            have : F < 0 := by simpa [hnzero] using hn
            linarith
          have hmpos : 0 < m := hnpos.trans_le hnm
          have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
          have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
          exact Real.strictMonoOn_log.monotoneOn hnR hmR
            (by exact_mod_cast hnm)
        linarith)).trans ih
  have hHm_lower : ∀ {n : ℕ}, 2 * F ≤ Real.log n →
      δ / 2 ≤ Hm n := by
    intro n hn
    have hnF : F < Real.log n := by linarith
    apply le_of_tendsto (by simpa [Hm, V] using hminusRatio)
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact hHm_tail hnF hnm
  intro n hn
  have hnpos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
    have : 2 * F ≤ 0 := by simpa [hnzero] using hn
    linarith
  have ht : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have htF : 0 < Real.log n - F := by linarith
  have htPlus : 0 < Real.log n + F := by linarith
  have hVlow : δ * (Real.log n - F)^2 ≤
      2 * V n := by
    have h := hHm_lower hn
    have h' : δ / 2 ≤ V n / (Real.log n - F)^2 := by
      simpa [Hm] using h
    have hh := (le_div_iff₀ (sq_pos_of_pos htF)).mp h'
    nlinarith
  have hVup : 2 * V n ≤ δ * (Real.log n + F)^2 := by
    have h := hHp_bound n
    have h' : V n / (Real.log n + F)^2 ≤ δ / 2 := by
      simpa [Hp] using h
    have hh := (div_le_iff₀ (sq_pos_of_pos htPlus)).mp h'
    nlinarith
  have hbaln := hbal (n := n) hnpos
  have hupp : 2 * V n ≤ (Real.log n + E) * M n := by
    have hh := (abs_le.mp (by simpa [V] using hbaln)).1
    change 2 * abstractVolterraIncrement M n ≤
      (Real.log n + E) * M n
    nlinarith [hh]
  have hlow : (Real.log n - E) * M n ≤ 2 * V n := by
    have hh := (abs_le.mp (by simpa [V] using hbaln)).2
    change (Real.log n - E) * M n ≤
      2 * abstractVolterraIncrement M n
    nlinarith [hh]
  have hA : δ * (Real.log n - F)^2 ≤
      (Real.log n + F) * M n := by
    have hEF : E ≤ F := by dsimp [F]; linarith [hlog2]
    have hmon : (Real.log n + E) * M n ≤
        (Real.log n + F) * M n := by
      gcongr
      exact hMnonneg n
    exact hVlow.trans (hupp.trans hmon)
  have hB : (Real.log n - F) * M n ≤
      δ * (Real.log n + F)^2 := by
    have hEF : E ≤ F := by dsimp [F]; linarith [hlog2]
    have hmon : (Real.log n - F) * M n ≤
        (Real.log n - E) * M n := by
      have hM := hMnonneg n
      nlinarith
    exact hmon.trans (hlow.trans hVup)
  have hpolyLower :
      (δ * Real.log n - 7 * δ * F) *
          (Real.log n + F) ≤ δ * (Real.log n - F)^2 := by
    have hδF : 0 ≤ δ * F := mul_nonneg hδ.le hF.le
    have hterm : 0 ≤ (δ * F) * Real.log n :=
      mul_nonneg hδF ht
    have hterm2 : 0 ≤ (δ * F) * F :=
      mul_nonneg hδF hF.le
    nlinarith
  have hpolyUpper :
      δ * (Real.log n + F)^2 ≤
        (δ * Real.log n + 7 * δ * F) *
          (Real.log n - F) := by
    have hδF : 0 ≤ δ * F := mul_nonneg hδ.le hF.le
    have ht2 : 0 ≤ Real.log n - 2 * F := by linarith
    nlinarith [mul_nonneg hδF ht2]
  have hlowerMul :
      (δ * Real.log n - 7 * δ * F) *
          (Real.log n + F) ≤ M n * (Real.log n + F) := by
    calc
      (δ * Real.log n - 7 * δ * F) * (Real.log n + F) ≤
          δ * (Real.log n - F)^2 := hpolyLower
      _ ≤ (Real.log n + F) * M n := hA
      _ = M n * (Real.log n + F) := by ring
  have hupperMul :
      (M n) * (Real.log n - F) ≤
        (δ * Real.log n + 7 * δ * F) * (Real.log n - F) := by
    calc
      M n * (Real.log n - F) =
          (Real.log n - F) * M n := by ring
      _ ≤ δ * (Real.log n + F)^2 := hB
      _ ≤ (δ * Real.log n + 7 * δ * F) *
          (Real.log n - F) := hpolyUpper
  have hlower : δ * Real.log n - 7 * δ * F ≤ M n :=
    le_of_mul_le_mul_right hlowerMul htPlus
  have hupper : M n ≤ δ * Real.log n + 7 * δ * F :=
    le_of_mul_le_mul_right hupperMul htF
  apply abs_le.mpr
  constructor <;> linarith

end BoundedGaps.Maynard
