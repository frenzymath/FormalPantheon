import BoundedGaps.Maynard.ConcreteFractionalRectangleSimplex

noncomputable section

namespace BoundedGaps.Maynard

open Filter Metric

theorem eventually_nat_le_engelsmaMaynardRadius_of_log_ratio_le
    {alpha beta gamma : ℝ} (halpha : 0 < alpha)
    (hbeta : 0 ≤ beta) (hbg : beta < gamma) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      0 < n →
      Real.log n / Real.log (engelsmaMaynardRadius alpha N) ≤ beta →
      n ≤ engelsmaMaynardRadius (alpha * gamma) N := by
  have hgamma : 0 < gamma := lt_of_le_of_lt hbeta hbg
  have hgap : 0 < gamma - beta := sub_pos.mpr hbg
  have hratio := tendsto_log_engelsmaMaynardRadius_ratio
    (mul_pos halpha hgamma) halpha
  have hratio' : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius (alpha * gamma) N) /
        Real.log (engelsmaMaynardRadius alpha N)) atTop (nhds gamma) := by
    have hlimit : alpha * gamma / alpha = gamma := by
      field_simp [halpha.ne']
    simpa [hlimit] using hratio
  have hratioEvent := hratio'.eventually
    (Metric.ball_mem_nhds gamma (show 0 < ((gamma - beta) / 2 : ℝ) by positivity))
  have hfull := eventually_one_lt_engelsmaMaynardRadius halpha
  have hupper := eventually_one_lt_engelsmaMaynardRadius
    (mul_pos halpha hgamma)
  filter_upwards [hratioEvent, hfull, hupper] with N hratioN hfullN hupperN
  have hfullLog : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hfullN)
  have hratioGt : beta <
      Real.log (engelsmaMaynardRadius (alpha * gamma) N) /
        Real.log (engelsmaMaynardRadius alpha N) := by
    have habs : |Real.log (engelsmaMaynardRadius (alpha * gamma) N) /
          Real.log (engelsmaMaynardRadius alpha N) - gamma| <
        (gamma - beta) / 2 := by
      simpa only [Real.dist_eq] using hratioN
    have hlow := (abs_lt.mp habs).1
    linarith
  intro n hn hlog
  by_contra hnot
  have hlt : engelsmaMaynardRadius (alpha * gamma) N < n :=
    Nat.lt_of_not_ge hnot
  have hupperReal : (engelsmaMaynardRadius (alpha * gamma) N : ℝ) < n := by
    exact_mod_cast hlt
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hupperLog : Real.log (engelsmaMaynardRadius (alpha * gamma) N) <
      Real.log n := by
    exact Real.strictMonoOn_log
      (by
        simp only [Set.mem_Ioi]
        exact_mod_cast (Nat.zero_lt_of_lt hupperN)) hnReal hupperReal
  have hratioLt :
      Real.log (engelsmaMaynardRadius (alpha * gamma) N) /
          Real.log (engelsmaMaynardRadius alpha N) <
        Real.log n / Real.log (engelsmaMaynardRadius alpha N) := by
    exact (div_lt_div_iff_of_pos_right hfullLog).2 hupperLog
  linarith

theorem eventually_log_ratio_lt_of_nat_le_engelsmaMaynardRadius
    {alpha beta gamma : ℝ} (halpha : 0 < alpha)
    (hbeta : 0 ≤ beta) (hbg : beta < gamma) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ≤ engelsmaMaynardRadius (alpha * beta) N →
      Real.log n / Real.log (engelsmaMaynardRadius alpha N) < gamma := by
  by_cases hzero : beta = 0
  · subst beta
    have hgamma : 0 < gamma := hbg
    filter_upwards [] with N
    intro n hn hnle
    have hnleOne : n ≤ 1 := by
      simpa [engelsmaMaynardRadius, maynardDivisorCutoff] using hnle
    have hnOne : n = 1 := by omega
    subst n
    simpa using hgamma
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
    have hratio := tendsto_log_engelsmaMaynardRadius_ratio
      (mul_pos halpha hbetaPos) halpha
    have hratio' : Tendsto (fun N : ℕ =>
        Real.log (engelsmaMaynardRadius (alpha * beta) N) /
          Real.log (engelsmaMaynardRadius alpha N)) atTop (nhds beta) := by
      have hlimit : alpha * beta / alpha = beta := by
        field_simp [halpha.ne']
      simpa [hlimit] using hratio
    have hgap : 0 < gamma - beta := sub_pos.mpr hbg
    have hratioEvent := hratio'.eventually
      (Metric.ball_mem_nhds beta
        (show 0 < ((gamma - beta) / 2 : ℝ) by positivity))
    have hfull := eventually_one_lt_engelsmaMaynardRadius halpha
    have hlower := eventually_one_lt_engelsmaMaynardRadius
      (mul_pos halpha hbetaPos)
    filter_upwards [hratioEvent, hfull, hlower] with
        N hratioN hfullN hlowerN
    have hfullLog : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
      Real.log_pos (by exact_mod_cast hfullN)
    have hratioLt :
        Real.log (engelsmaMaynardRadius (alpha * beta) N) /
          Real.log (engelsmaMaynardRadius alpha N) < gamma := by
      have habs : |Real.log (engelsmaMaynardRadius (alpha * beta) N) /
            Real.log (engelsmaMaynardRadius alpha N) - beta| <
          (gamma - beta) / 2 := by
        simpa only [Real.dist_eq] using hratioN
      have hupp := (abs_lt.mp habs).2
      linarith
    intro n hn hnle
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hlowerReal : (0 : ℝ) <
        engelsmaMaynardRadius (alpha * beta) N := by
      exact_mod_cast (Nat.zero_lt_of_lt hlowerN)
    have hnleReal : (n : ℝ) ≤
        engelsmaMaynardRadius (alpha * beta) N := by exact_mod_cast hnle
    have hlogle : Real.log n ≤
        Real.log (engelsmaMaynardRadius (alpha * beta) N) :=
      Real.strictMonoOn_log.monotoneOn hnReal hlowerReal hnleReal
    have hdivle : Real.log n /
          Real.log (engelsmaMaynardRadius alpha N) ≤
        Real.log (engelsmaMaynardRadius (alpha * beta) N) /
          Real.log (engelsmaMaynardRadius alpha N) :=
      (div_le_div_iff_of_pos_right hfullLog).2 hlogle
    exact hdivle.trans_lt hratioLt

end BoundedGaps.Maynard
