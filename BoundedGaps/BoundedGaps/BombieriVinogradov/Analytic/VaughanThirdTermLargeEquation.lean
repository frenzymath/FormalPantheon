import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermLargeConclusion

/-!
# Equation (6.13) for Vaughan's large third term

This file performs the finite dyadic summation after the per-block maximal
estimate and exports the non-strict robust form and strict source-context form
of AkbaryHambrook2013v2, equation (6.13).

Semantic review: `SEM-456`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Weighted endpoint maxima are bounded by the sum of the separately
weighted dyadic block maxima.  The maximizing endpoint remains inside each
primitive-character summand. -/
theorem sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
      ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
  classical
  let scales := vaughanThirdLargeDyadicExponents U V x
  let weight : ℕ → ℝ := fun q ↦ (q : ℝ) / (q.totient : ℝ)
  have hendpoint :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
    apply Finset.sum_le_sum
    intro q _hq
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro chi _hchi
      exact
        vaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
          hU hV hx chi.1
    · dsimp only [weight]
      positivity
  have hreorder :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1) =
        ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
    have hperq (q : ℕ) :
        weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 =
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    calc
      _ = ∑ q ∈ Finset.Ioc 0 Q,
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hperq q
      _ = _ := Finset.sum_comm
  calc
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
      simpa only [weight] using hendpoint
    _ = ∑ alpha ∈ scales,
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := hreorder
    _ = _ := by rfl

/-- Robust all-`Q` form of Akbary--Hambrook equation (6.13). -/
theorem sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
      akbaryHambrookC3 / Real.log 2 *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) +
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        (Real.log (2 * U * V)) ^ 2 * Real.log (4 * (x : ℝ)) := by
  classical
  let scales := vaughanThirdLargeDyadicExponents U V x
  let A : ℝ := (x : ℝ) +
    (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) +
    Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
    (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
  let L : ℝ := Real.log (2 * U * V)
  let Xlog : ℝ := Real.log (4 * (x : ℝ))
  let C : ℝ := akbaryHambrookC3 * A * L * Xlog
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hxOne : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hLpos : 0 < L := by
    dsimp only [L]
    apply Real.log_pos
    nlinarith [mul_pos hUpos hVpos]
  have hXlogPos : 0 < Xlog := by
    dsimp only [Xlog]
    exact Real.log_pos (by nlinarith)
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity [akbaryHambrookC3_pos]
  have hbridge :=
    sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
      (U := U) (V := V) (x := x) (Q := Q) hx hU hV
  have hsum :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
        ∑ _alpha ∈ scales, C := by
    apply hbridge.trans
    apply Finset.sum_le_sum
    intro alpha halpha
    let M : ℕ := 2 ^ alpha
    have hMpos : 0 < M := by positivity
    have hmReal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    rcases Finset.mem_filter.mp halpha with
      ⟨_halphaRange, hMlower, hMupper, _hMx⟩
    change U / 2 < (M : ℝ) at hMlower
    change (M : ℝ) ≤ U * V at hMupper
    have hroot :
        Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          Real.sqrt ((x : ℝ) * U * V) := by
      apply Real.sqrt_le_sqrt
      calc
        (x : ℝ) * (M : ℝ) ≤ (x : ℝ) * (U * V) :=
          mul_le_mul_of_nonneg_left hMupper hxReal.le
        _ = (x : ℝ) * U * V := by ring
    have hUtwoM : U ≤ 2 * (M : ℝ) := by linarith
    have hsqrtUle : Real.sqrt U ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) := by
      calc
        Real.sqrt U ≤ Real.sqrt (2 * (M : ℝ)) :=
          Real.sqrt_le_sqrt hUtwoM
        _ = Real.sqrt 2 * Real.sqrt (M : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrtUpos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
    have hsqrtMpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hmReal
    have hinv : 1 / Real.sqrt (M : ℝ) ≤
        Real.sqrt 2 / Real.sqrt U := by
      apply (div_le_div_iff₀ hsqrtMpos hsqrtUpos).2
      simpa only [one_mul] using hsqrtUle
    have hrootTerm :
        (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) :=
      mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg Q)
    have hinvTerm :
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) ≤
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by
      calc
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) =
            ((Q : ℝ) * (x : ℝ)) *
              (1 / Real.sqrt (M : ℝ)) := by ring
        _ ≤ ((Q : ℝ) * (x : ℝ)) *
            (Real.sqrt 2 / Real.sqrt U) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by ring
    have hAblock :
        (x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) ≤ A := by
      dsimp only [A]
      linarith
    have hlog : Real.log (2 * (M : ℝ)) ≤ L := by
      dsimp only [L]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hAblockNonneg : 0 ≤
        (x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
          (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) := by positivity
    have hlogMNonneg : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ 2 * M by omega))
    calc
      _ ≤ akbaryHambrookC3 *
          ((x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
          Real.log (2 * (M : ℝ)) * Xlog := by
        simpa only [scales, M, Xlog] using
          (sum_weighted_vaughanThirdLargeDyadicBlockMaximum_le
            (U := U) (V := V) (x := x) (Q := Q) (alpha := alpha)
            hx hU hV halpha)
      _ ≤ C := by
        dsimp only [C]
        calc
          _ ≤ akbaryHambrookC3 * A * Real.log (2 * (M : ℝ)) * Xlog := by
            apply mul_le_mul_of_nonneg_right _ hXlogPos.le
            apply mul_le_mul_of_nonneg_right _ hlogMNonneg
            exact mul_le_mul_of_nonneg_left hAblock
              akbaryHambrookC3_pos.le
          _ ≤ akbaryHambrookC3 * A * L * Xlog := by
            apply mul_le_mul_of_nonneg_right _ hXlogPos.le
            exact mul_le_mul_of_nonneg_left hlog
              (mul_nonneg akbaryHambrookC3_pos.le hAnonneg)
  have hcard := card_vaughanThirdLargeDyadicExponents_le_log hU hV x
  change ((scales.card : ℕ) : ℝ) ≤ L / Real.log 2 at hcard
  calc
    _ ≤ ∑ _alpha ∈ scales, C := hsum
    _ = (scales.card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L / Real.log 2) * C :=
      mul_le_mul_of_nonneg_right hcard hCnonneg
    _ = akbaryHambrookC3 / Real.log 2 * A * L ^ 2 * Xlog := by ring
    _ = _ := by rfl

/-- Source-context strict form of Akbary--Hambrook equation (6.13). -/
theorem sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_lt
    {U V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hQ : 2 ≤ Q) (_hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) <
      akbaryHambrookC3 / Real.log 2 *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) +
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        (Real.log (2 * U * V)) ^ 2 * Real.log (4 * (x : ℝ)) := by
  classical
  let scales := vaughanThirdLargeDyadicExponents U V x
  let A : ℝ := (x : ℝ) +
    (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) +
    Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
    (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
  let L : ℝ := Real.log (2 * U * V)
  let Xlog : ℝ := Real.log (4 * (x : ℝ))
  let C : ℝ := akbaryHambrookC3 * A * L * Xlog
  have hxOne : 1 ≤ x := by omega
  have hxReal : 0 < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have hxFour : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hQReal : 0 < (Q : ℝ) := by
    exact_mod_cast (show 0 < Q by omega)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hLpos : 0 < L := by
    dsimp only [L]
    apply Real.log_pos
    nlinarith [mul_pos hUpos hVpos]
  have hXlogPos : 0 < Xlog := by
    dsimp only [Xlog]
    exact Real.log_pos (by nlinarith)
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity [akbaryHambrookC3_pos]
  have hbridge :=
    sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
      (U := U) (V := V) (x := x) (Q := Q) hxOne hU hV
  by_cases hscales : scales = ∅
  · have hleft :
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤ 0 := by
      simpa only [scales, hscales, Finset.sum_empty] using hbridge
    have hright : 0 <
        akbaryHambrookC3 / Real.log 2 * A * L ^ 2 * Xlog := by
      positivity [akbaryHambrookC3_pos]
    exact hleft.trans_lt (by simpa only [A, L, Xlog] using hright)
  have hscalesNonempty : scales.Nonempty := Finset.nonempty_iff_ne_empty.mpr hscales
  have hsumStrict :
      (∑ alpha ∈ scales,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1) <
        ∑ _alpha ∈ scales, C := by
    apply Finset.sum_lt_sum_of_nonempty hscalesNonempty
    intro alpha halpha
    let M : ℕ := 2 ^ alpha
    have hMpos : 0 < M := by positivity
    have hmReal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    rcases Finset.mem_filter.mp halpha with
      ⟨_halphaRange, hMlower, hMupper, _hMx⟩
    change U / 2 < (M : ℝ) at hMlower
    change (M : ℝ) ≤ U * V at hMupper
    have hroot :
        Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          Real.sqrt ((x : ℝ) * U * V) := by
      apply Real.sqrt_le_sqrt
      calc
        (x : ℝ) * (M : ℝ) ≤ (x : ℝ) * (U * V) :=
          mul_le_mul_of_nonneg_left hMupper hxReal.le
        _ = (x : ℝ) * U * V := by ring
    have hUtwoM : U < 2 * (M : ℝ) := by linarith
    have hsqrtUstrict :
        Real.sqrt U < Real.sqrt 2 * Real.sqrt (M : ℝ) := by
      calc
        Real.sqrt U < Real.sqrt (2 * (M : ℝ)) :=
          Real.sqrt_lt_sqrt hUpos.le hUtwoM
        _ = Real.sqrt 2 * Real.sqrt (M : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrtUpos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
    have hsqrtMpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hmReal
    have hinvStrict : 1 / Real.sqrt (M : ℝ) <
        Real.sqrt 2 / Real.sqrt U := by
      apply (div_lt_div_iff₀ hsqrtMpos hsqrtUpos).2
      simpa only [one_mul] using hsqrtUstrict
    have hrootTerm :
        (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) :=
      mul_le_mul_of_nonneg_left hroot hQReal.le
    have hinvTerm :
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) <
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by
      calc
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) =
            ((Q : ℝ) * (x : ℝ)) *
              (1 / Real.sqrt (M : ℝ)) := by ring
        _ < ((Q : ℝ) * (x : ℝ)) *
            (Real.sqrt 2 / Real.sqrt U) :=
          mul_lt_mul_of_pos_left hinvStrict (mul_pos hQReal hxReal)
        _ = Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by ring
    have hAblock :
        (x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) < A := by
      dsimp only [A]
      linarith
    have hlog : Real.log (2 * (M : ℝ)) ≤ L := by
      dsimp only [L]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hlogMpos : 0 < Real.log (2 * (M : ℝ)) :=
      Real.log_pos (by
        exact_mod_cast (show 1 < 2 * M by omega))
    have hblock :=
      sum_weighted_vaughanThirdLargeDyadicBlockMaximum_le
        (U := U) (V := V) (x := x) (Q := Q) (alpha := alpha)
        hxOne hU hV halpha
    apply hblock.trans_lt
    calc
      akbaryHambrookC3 *
          ((x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
          Real.log (2 * (M : ℝ)) * Xlog <
          akbaryHambrookC3 * A * Real.log (2 * (M : ℝ)) * Xlog := by
        gcongr
        exact akbaryHambrookC3_pos
      _ ≤ C := by
        dsimp only [C]
        apply mul_le_mul_of_nonneg_right _ hXlogPos.le
        exact mul_le_mul_of_nonneg_left hlog
          (mul_nonneg akbaryHambrookC3_pos.le hApos.le)
  have hcard := card_vaughanThirdLargeDyadicExponents_le_log hU hV x
  change ((scales.card : ℕ) : ℝ) ≤ L / Real.log 2 at hcard
  calc
    _ ≤ ∑ alpha ∈ scales,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := hbridge
    _ < ∑ _alpha ∈ scales, C := hsumStrict
    _ = (scales.card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L / Real.log 2) * C :=
      mul_le_mul_of_nonneg_right hcard hCpos.le
    _ = akbaryHambrookC3 / Real.log 2 * A * L ^ 2 * Xlog := by ring
    _ = _ := by rfl

end

end BoundedGaps.Maynard
