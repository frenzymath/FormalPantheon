import BoundedGaps.BombieriVinogradov.Analytic.BilinearLargeSieve
import BoundedGaps.BombieriVinogradov.Analytic.BilinearPerronAggregate
import BoundedGaps.BombieriVinogradov.Analytic.PerronEnvelopeIntegral

/-!
# The maximal bilinear character large sieve

This file applies the rectangular large sieve inside equation (6.4),
evaluates the Perron envelope, and proves the optimized constant in
AkbaryHambrook2013v2, Lemma 6.1 and equation (6.5), printed pp. 17--18.

Semantic review: `SEM-455`.
-/

open MeasureTheory
open scoped Interval BigOperators

namespace BoundedGaps.Maynard

noncomputable section

/-- The logarithmic phases in the Perron integral preserve both coefficient
energies in the rectangular bilinear large sieve. -/
theorem sum_weighted_norm_bilinear_natLogTwists_subset_Ioc_le
    (Q m0 M n0 N : ℕ) (sm sn : Finset ℕ)
    (hsm : sm ⊆ Finset.Ioc m0 (m0 + M))
    (hsn : sn ⊆ Finset.Ioc n0 (n0 + N))
    (a b : ℕ → ℂ) (t : ℝ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) *
              (b n * natLogTwist n t) * psi.1 (m * n)‖) ≤
      Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2) := by
  simpa only [norm_mul, norm_natLogTwist, mul_one] using
    sum_weighted_norm_bilinear_primitiveTwists_subset_Ioc_le
      Q m0 M n0 N sm sn hsm hsn
        (fun m ↦ a m * natLogTwist m t)
        (fun n ↦ b n * natLogTwist n t)

private theorem sum_norm_le_sqrt_card_mul_sqrt_sum_sq
    {α : Type*} (s : Finset α) (a : α → ℂ) :
    (∑ x ∈ s, ‖a x‖) ≤
      Real.sqrt (s.card : ℝ) * Real.sqrt (∑ x ∈ s, ‖a x‖ ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun x ↦ ‖a x‖) (fun _x ↦ (1 : ℝ))
  simpa only [mul_one, one_pow, Finset.sum_const_zero, Finset.sum_const,
    nsmul_eq_mul, mul_comm] using h

private theorem sum_norm_le_sqrt_span_mul_sqrt_sum_sq
    {m0 M : ℕ} (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + M)) (a : ℕ → ℂ) :
    (∑ x ∈ s, ‖a x‖) ≤
      Real.sqrt (M : ℝ) * Real.sqrt (∑ x ∈ s, ‖a x‖ ^ 2) := by
  have hcardNat : s.card ≤ M := by
    have h := Finset.card_le_card hs
    simpa only [Nat.card_Ioc, Nat.add_sub_cancel_left] using h
  have hcardReal : (s.card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hcardNat
  exact (sum_norm_le_sqrt_card_mul_sqrt_sum_sq s a).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcardReal)
      (Real.sqrt_nonneg _))

private theorem sq_le_sqrt_add_sq_mul_sqrt_add_sq
    (M N Q : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    Q ^ 2 ≤ Real.sqrt (M + Q ^ 2) * Real.sqrt (N + Q ^ 2) := by
  have hQM : Q ≤ Real.sqrt (M + Q ^ 2) := by
    rw [Real.le_sqrt hQ (by positivity)]
    linarith
  have hQN : Q ≤ Real.sqrt (N + Q ^ 2) := by
    rw [Real.le_sqrt hQ (by positivity)]
    linarith
  simpa only [pow_two] using
    mul_le_mul hQM hQN hQ (Real.sqrt_nonneg _)

private theorem sqrt_spans_le_sqrt_productCap
    (m0 M n0 N : ℕ) :
    Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) ≤
      Real.sqrt (((m0 + M) * (n0 + N) : ℕ) : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg M)]
  apply Real.sqrt_le_sqrt
  norm_cast
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The exact constant `c3` in Akbary--Hambrook Lemma 6.1. -/
noncomputable def akbaryHambrookC3 : ℝ :=
  2 / Real.pi *
    (2 + Real.log (Real.log 2 / Real.log (4 / 3 : ℝ))) /
      Real.log 2

/-- The optimizing Perron radius `P^(3/2) / log(4/3)`, written without a
fractional-power convention. -/
noncomputable def akbaryHambrookPerronTime (P : ℝ) : ℝ :=
  P * Real.sqrt P / Real.log (4 / 3 : ℝ)

theorem akbaryHambrookPerronTime_pos
    {P : ℝ} (hP : 1 ≤ P) :
    0 < akbaryHambrookPerronTime P := by
  unfold akbaryHambrookPerronTime
  positivity

/-- The optimized Perron radius lies in the large-envelope regime. -/
theorem one_le_akbaryHambrookPerronTime_mul_log
    {P : ℝ} (hP : 1 ≤ P) :
    1 ≤ akbaryHambrookPerronTime P * Real.log (2 * P) := by
  have hc : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt P := Real.one_le_sqrt.mpr hP
  have hscale : 1 ≤ P * Real.sqrt P := by
    simpa using mul_le_mul hP hsqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have harg : (4 / 3 : ℝ) ≤ 2 * P := by nlinarith
  have hlog : Real.log (4 / 3 : ℝ) ≤ Real.log (2 * P) :=
    Real.log_le_log (by norm_num) harg
  have hratio : 1 ≤ Real.log (2 * P) / Real.log (4 / 3 : ℝ) :=
    (le_div_iff₀ hc).2 (by simpa using hlog)
  unfold akbaryHambrookPerronTime
  calc
    P * Real.sqrt P / Real.log (4 / 3 : ℝ) * Real.log (2 * P) =
        (P * Real.sqrt P) *
          (Real.log (2 * P) / Real.log (4 / 3 : ℝ)) := by ring
    _ ≥ 1 * 1 := mul_le_mul hscale hratio (by norm_num) (by positivity)
    _ = 1 := one_mul 1

private theorem log_affine_div_le_at_left
    {A l x : ℝ} (hl : 0 < l) (hlx : l ≤ x)
    (hA : 1 ≤ A + Real.log l) :
    (A + Real.log x) / x ≤ (A + Real.log l) / l := by
  have hx : 0 < x := hl.trans_le hlx
  have hlog : Real.log x - Real.log l ≤ x / l - 1 := by
    rw [← Real.log_div hx.ne' hl.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hx hl)
  have hlog' : l * (Real.log x - Real.log l) ≤ x - l := by
    calc
      l * (Real.log x - Real.log l) ≤ l * (x / l - 1) :=
        mul_le_mul_of_nonneg_left hlog hl.le
      _ = x - l := by field_simp
  have hdelta : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hdelta' : x - l ≤ (x - l) * (A + Real.log l) :=
    le_mul_of_one_le_right hdelta hA
  rw [div_le_div_iff₀ hx hl]
  calc
    (A + Real.log x) * l =
        (A + Real.log l) * l + l * (Real.log x - Real.log l) := by ring
    _ ≤ (A + Real.log l) * l + (x - l) := by gcongr
    _ ≤ (A + Real.log l) * l + (x - l) * (A + Real.log l) := by gcongr
    _ = (A + Real.log l) * x := by ring

private theorem optimized_log_constant_lower_bound :
    1 ≤
      (2 - (3 / 2 : ℝ) * Real.log 2 - Real.log (Real.log (4 / 3 : ℝ))) +
        Real.log (Real.log 2) := by
  have hc : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoc : 2 * Real.log (4 / 3 : ℝ) ≤ Real.log 2 := by
    calc
      2 * Real.log (4 / 3 : ℝ) = Real.log ((4 / 3 : ℝ) ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 2 := Real.log_le_log (by positivity) (by norm_num)
  have hratio : (2 : ℝ) ≤ Real.log 2 / Real.log (4 / 3 : ℝ) := by
    rw [le_div_iff₀ hc]
    exact htwoc
  have hlogratio : Real.log 2 ≤
      Real.log (Real.log 2 / Real.log (4 / 3 : ℝ)) :=
    Real.log_le_log (by norm_num) hratio
  have hl_one : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    1 ≤ 2 - (3 / 2 : ℝ) * Real.log 2 + Real.log 2 := by linarith
    _ ≤ 2 - (3 / 2 : ℝ) * Real.log 2 +
        Real.log (Real.log 2 / Real.log (4 / 3 : ℝ)) := by linarith
    _ = (2 - (3 / 2 : ℝ) * Real.log 2 -
          Real.log (Real.log (4 / 3 : ℝ))) +
        Real.log (Real.log 2) := by
      rw [Real.log_div hl.ne' hc.ne']
      ring

/-- The exact real form of equation (6.5), at the source's optimizing Perron
radius. The reciprocal `log(2P)` normalizes the entire parenthesis. -/
theorem akbaryHambrook_equation_six_five
    {P : ℝ} (hP : 1 ≤ P) :
    2 / Real.pi *
        (Real.log
            (Real.exp 1 * akbaryHambrookPerronTime P *
              Real.log (2 * P)) +
          P * Real.sqrt P /
            (Real.log (4 / 3 : ℝ) * akbaryHambrookPerronTime P)) /
        Real.log (2 * P) ≤
      akbaryHambrookC3 := by
  let c : ℝ := Real.log (4 / 3 : ℝ)
  let l : ℝ := Real.log 2
  let x : ℝ := Real.log (2 * P)
  let A : ℝ := 2 - (3 / 2 : ℝ) * l - Real.log c
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hsqrt : 0 < Real.sqrt P := Real.sqrt_pos.2 hPpos
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hl : 0 < l := Real.log_pos (by norm_num)
  have htwoP : (2 : ℝ) ≤ 2 * P := by nlinarith
  have hx : 0 < x := Real.log_pos (by nlinarith)
  have hlx : l ≤ x := Real.log_le_log (by norm_num) htwoP
  have hlogP : x = l + Real.log P := by
    dsimp only [x, l]
    rw [Real.log_mul (by norm_num) hPpos.ne']
  have hsecond :
      P * Real.sqrt P /
          (c * akbaryHambrookPerronTime P) = 1 := by
    dsimp only [akbaryHambrookPerronTime, c]
    field_simp
  have hlogTime :
      Real.log (akbaryHambrookPerronTime P) =
        Real.log P + Real.log (Real.sqrt P) - Real.log c := by
    rw [akbaryHambrookPerronTime,
      Real.log_div (mul_ne_zero hPpos.ne' hsqrt.ne') hc.ne',
      Real.log_mul hPpos.ne' hsqrt.ne']
  have hlogArg :
      Real.log (Real.exp 1 * akbaryHambrookPerronTime P * x) =
        1 + (3 / 2 : ℝ) * Real.log P - Real.log c + Real.log x := by
    rw [show Real.exp 1 * akbaryHambrookPerronTime P * x =
        Real.exp 1 * (akbaryHambrookPerronTime P * x) by ring,
      Real.log_mul (Real.exp_ne_zero 1)
        (mul_ne_zero (akbaryHambrookPerronTime_pos hP).ne' hx.ne'),
      Real.log_exp,
      Real.log_mul (akbaryHambrookPerronTime_pos hP).ne' hx.ne', hlogTime,
      Real.log_sqrt hPpos.le]
    ring
  have hnorm :
      Real.log (Real.exp 1 * akbaryHambrookPerronTime P * x) +
          P * Real.sqrt P /
            (c * akbaryHambrookPerronTime P) =
        (3 / 2 : ℝ) * x + A + Real.log x := by
    rw [hlogArg, hsecond]
    dsimp only [A]
    rw [hlogP]
    ring
  have hA : 1 ≤ A + Real.log l := by
    simpa only [A, l, c] using optimized_log_constant_lower_bound
  have hmain : (A + Real.log x) / x ≤ (A + Real.log l) / l :=
    log_affine_div_le_at_left hl hlx hA
  unfold akbaryHambrookC3
  change 2 / Real.pi *
      (Real.log (Real.exp 1 * akbaryHambrookPerronTime P * x) +
        P * Real.sqrt P / (c * akbaryHambrookPerronTime P)) / x ≤ _
  rw [hnorm]
  calc
    2 / Real.pi * ((3 / 2 : ℝ) * x + A + Real.log x) / x =
        2 / Real.pi * ((3 / 2 : ℝ) + (A + Real.log x) / x) := by
      field_simp
      ring
    _ ≤ 2 / Real.pi * ((3 / 2 : ℝ) + (A + Real.log l) / l) := by
      gcongr
    _ = 2 / Real.pi *
        (2 + Real.log (Real.log 2 / Real.log (4 / 3 : ℝ))) /
          Real.log 2 := by
      dsimp only [A, l, c]
      rw [Real.log_div hl.ne' hc.ne']
      field_simp
      ring

/-- Equation (6.4) after the pointwise rectangular large sieve, coefficient
Cauchy--Schwarz, and exact large-regime envelope integration. -/
theorem sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_preoptimized
    (Q m0 M n0 N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (sm sn : Finset ℕ)
    (hsm : sm ⊆ Finset.Ioc m0 (m0 + M))
    (hsn : sn ⊆ Finset.Ioc n0 (n0 + N))
    (a b : ℕ → ℂ) {T : ℝ} (hT : 0 < T)
    (hregime :
      1 ≤ T * Real.log
        (2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ))) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          bilinearProductCutoffMaximum
            ((m0 + M) * (n0 + N)) q psi.1 sm sn a b) ≤
      (Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2)) *
      (2 / Real.pi * Real.log
          (Real.exp 1 * T *
            Real.log
              (2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ))) +
        2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ) *
            Real.sqrt (((m0 + M) * (n0 + N) : ℕ) : ℝ) /
          (Real.pi * Real.log (4 / 3 : ℝ) * T)) := by
  let K : ℕ := (m0 + M) * (n0 + N)
  let P : ℝ := (K : ℝ)
  let B : ℝ := Real.log (2 * P)
  let D : ℝ := Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
    Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2)
  let EA : ℝ := Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2)
  let EB : ℝ := Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2)
  let G : ℝ := D * EA * EB
  let LA : ℝ := ∑ m ∈ sm, ‖a m‖
  let LB : ℝ := ∑ n ∈ sn, ‖b n‖
  let S : ℝ → ℝ := fun t ↦
    ∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) *
              (b n * natLogTwist n t) * psi.1 (m * n)‖
  let I : ℝ := ∫ t in -T..T, perronEnvelope B t * S t
  let L : ℝ := ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        bilinearProductCutoffMaximum K q psi.1 sm sn a b
  have hK : 0 < K := by
    exact Nat.mul_pos (by omega) (by omega)
  have hP : 1 ≤ P := by
    dsimp only [P]
    exact_mod_cast hK
  have hB : 0 < B := by
    dsimp only [B]
    exact Real.log_pos (by nlinarith)
  have hS : Continuous S := by
    dsimp only [S, natLogTwist]
    fun_prop
  have hphase (t : ℝ) : S t ≤ G := by
    simpa only [S, G, D, EA, EB] using
      sum_weighted_norm_bilinear_natLogTwists_subset_Ioc_le
        Q m0 M n0 N sm sn hsm hsn a b t
  have hI : I ≤ 2 * Real.log (Real.exp 1 * T * B) * G := by
    have hf : IntervalIntegrable (fun t ↦ perronEnvelope B t * S t)
        volume (-T) T :=
      ((continuous_perronEnvelope hB.le).mul hS).intervalIntegrable _ _
    have hg : IntervalIntegrable (fun t ↦ perronEnvelope B t * G)
        volume (-T) T :=
      ((continuous_perronEnvelope hB.le).mul continuous_const).intervalIntegrable _ _
    calc
      I ≤ ∫ t in -T..T, perronEnvelope B t * G := by
        dsimp only [I]
        exact intervalIntegral.integral_mono_on (by linarith) hf hg
          (fun t _ht ↦ mul_le_mul_of_nonneg_left (hphase t)
            (perronEnvelope_nonneg B t))
      _ = (∫ t in -T..T, perronEnvelope B t) * G := by
        rw [intervalIntegral.integral_mul_const]
      _ = 2 * Real.log (Real.exp 1 * T * B) * G := by
        rw [integral_perronEnvelope_eq_two_mul_log hB hT]
        simpa only [B, P, K] using hregime
  have hbase : L ≤
      1 / Real.pi * I +
        2 * P * (Q : ℝ) ^ 2 /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) * LA * LB := by
    simpa only [L, I, S, B, P, K, LA, LB] using
      sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le
        Q m0 M n0 N hM hN sm sn hsm hsn a b hT
  have hmain : 1 / Real.pi * I ≤
      G * (2 / Real.pi * Real.log (Real.exp 1 * T * B)) := by
    calc
      1 / Real.pi * I ≤
          1 / Real.pi *
            (2 * Real.log (Real.exp 1 * T * B) * G) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ = G * (2 / Real.pi * Real.log (Real.exp 1 * T * B)) := by ring
  have hLA : LA ≤ Real.sqrt (M : ℝ) * EA := by
    simpa only [LA, EA] using
      sum_norm_le_sqrt_span_mul_sqrt_sum_sq sm hsm a
  have hLB : LB ≤ Real.sqrt (N : ℝ) * EB := by
    simpa only [LB, EB] using
      sum_norm_le_sqrt_span_mul_sqrt_sum_sq sn hsn b
  have hQL : (Q : ℝ) ^ 2 ≤ D := by
    simpa only [D] using sq_le_sqrt_add_sq_mul_sqrt_add_sq
      (M : ℝ) (N : ℝ) (Q : ℝ) (by positivity) (by positivity) (by positivity)
  have hspan : Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) ≤ Real.sqrt P := by
    simpa only [P, K] using sqrt_spans_le_sqrt_productCap m0 M n0 N
  have hLALB : LA * LB ≤
      Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) * EA * EB := by
    calc
      LA * LB ≤ (Real.sqrt (M : ℝ) * EA) *
          (Real.sqrt (N : ℝ) * EB) :=
        mul_le_mul hLA hLB (by positivity) (by positivity)
      _ = Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) * EA * EB := by ring
  have hcore : (Q : ℝ) ^ 2 * LA * LB ≤ D * Real.sqrt P * EA * EB := by
    calc
      (Q : ℝ) ^ 2 * LA * LB ≤ D *
          (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) * EA * EB) := by
        calc
          (Q : ℝ) ^ 2 * LA * LB = (Q : ℝ) ^ 2 * (LA * LB) := by ring
          _ ≤ D * (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) * EA * EB) :=
            mul_le_mul hQL hLALB (by positivity) (by positivity)
      _ ≤ D * (Real.sqrt P * EA * EB) := by gcongr
      _ = D * Real.sqrt P * EA * EB := by ring
  have herror :
      2 * P * (Q : ℝ) ^ 2 /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) * LA * LB ≤
        G * (2 * P * Real.sqrt P /
          (Real.pi * Real.log (4 / 3 : ℝ) * T)) := by
    have hc : 0 ≤ 2 * P /
        (Real.pi * Real.log (4 / 3 : ℝ) * T) := by positivity
    calc
      2 * P * (Q : ℝ) ^ 2 /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) * LA * LB =
          (2 * P / (Real.pi * Real.log (4 / 3 : ℝ) * T)) *
            ((Q : ℝ) ^ 2 * LA * LB) := by ring
      _ ≤ (2 * P / (Real.pi * Real.log (4 / 3 : ℝ) * T)) *
          (D * Real.sqrt P * EA * EB) :=
        mul_le_mul_of_nonneg_left hcore hc
      _ = G * (2 * P * Real.sqrt P /
          (Real.pi * Real.log (4 / 3 : ℝ) * T)) := by
        dsimp only [G]
        ring
  change L ≤ G *
    (2 / Real.pi * Real.log (Real.exp 1 * T * B) +
      2 * P * Real.sqrt P /
        (Real.pi * Real.log (4 / 3 : ℝ) * T))
  calc
    L ≤ 1 / Real.pi * I +
        2 * P * (Q : ℝ) ^ 2 /
          (Real.pi * Real.log (4 / 3 : ℝ) * T) * LA * LB := hbase
    _ ≤ G * (2 / Real.pi * Real.log (Real.exp 1 * T * B)) +
        G * (2 * P * Real.sqrt P /
          (Real.pi * Real.log (4 / 3 : ℝ) * T)) := add_le_add hmain herror
    _ = G *
        (2 / Real.pi * Real.log (Real.exp 1 * T * B) +
          2 * P * Real.sqrt P /
            (Real.pi * Real.log (4 / 3 : ℝ) * T)) := by ring

end

end BoundedGaps.Maynard
