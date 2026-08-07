import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermLargeEnergy

/-!
# Vaughan's large third-term conclusion

This file applies the optimized maximal bilinear large sieve on each active
dyadic block and proves the numerical block estimate used in
AkbaryHambrook2013v2, equation (6.13), with the source corrections recorded
in `SEM-456`.  The final equation is proved in
`VaughanThirdTermLargeEquation.lean`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Numerical maximal estimate for one active dyadic block. -/
theorem sum_weighted_vaughanThirdLargeDyadicBlockMaximum_le
    {U V : ℝ} {x Q alpha : ℕ}
    (_hx : 1 ≤ x) (_hU : 1 ≤ U) (_hV : 1 ≤ V)
    (halpha : alpha ∈ vaughanThirdLargeDyadicExponents U V x) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi) ≤
      akbaryHambrookC3 *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (2 ^ alpha : ℕ)) +
          (Q : ℝ) * (x : ℝ) /
            Real.sqrt ((2 ^ alpha : ℕ) : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) *
        Real.log (4 * (x : ℝ)) := by
  classical
  let M : ℕ := 2 ^ alpha
  let R : ℕ := x / M
  have hM : 0 < M := by positivity
  have hMlt : M < x := by
    rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
    dsimp only [M] at halphaBounds
    exact halphaBounds.2.2
  have hR : 0 < R := Nat.div_pos hMlt.le hM
  have hsm : vaughanThirdLargeDyadicIndices U V x alpha ⊆
      Finset.Ioc M (M + M) := by
    intro t ht
    have htBlock := (Finset.mem_inter.mp ht).2
    rw [dyadicBlock, Finset.mem_Ioc] at htBlock
    rw [Finset.mem_Ioc]
    constructor
    · simpa only [M] using htBlock.1
    · calc
        t ≤ 2 ^ (alpha + 1) := htBlock.2
        _ = M + M := by
          rw [pow_succ]
          dsimp only [M]
          omega
  have hsn : vaughanThirdLargeDyadicRIndices x alpha ⊆
      Finset.Ioc 0 (0 + R) := by
    intro r hr
    rw [vaughanThirdLargeDyadicRIndices, Finset.mem_Icc] at hr
    rw [Finset.mem_Ioc]
    constructor
    · omega
    · simpa only [R, M, zero_add] using hr.2
  have hblock :=
    sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
      Q M M 0 R hM hR
      (vaughanThirdLargeDyadicIndices U V x alpha)
      (vaughanThirdLargeDyadicRIndices x alpha)
      hsm hsn
      (fun t ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
      (fun _ ↦ (1 : ℂ))
  have hcardR : (vaughanThirdLargeDyadicRIndices x alpha).card = R := by
    rw [vaughanThirdLargeDyadicRIndices, Nat.card_Icc]
    simp [R, M]
  have hraw :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi) ≤
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
            ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) *
          Real.sqrt (R : ℝ) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
    simpa only [vaughanThirdLargeDyadicBlockMaximum, M, R, zero_add,
      norm_one, one_pow, Finset.sum_const, hcardR, Nat.cast_id,
      nsmul_eq_mul, mul_one] using hblock
  have henergy :=
    sqrt_sum_norm_sq_vaughanThirdCoefficient_dyadic_le U V x alpha
  have henergy' :
      Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
        ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) ≤
        Real.sqrt (M : ℝ) * Real.log (2 * (M : ℝ)) := by
    simpa only [M] using henergy
  have hMRNat : M * R ≤ x := by
    simpa only [R, Nat.mul_comm] using Nat.div_mul_le_self x M
  have hMR : (M : ℝ) * (R : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hMRNat
  have hcap :
      2 * ((((M + M) * R : ℕ) : ℝ)) ≤ 4 * (x : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add]
    nlinarith
  have hlogCap :
      Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) ≤
        Real.log (4 * (x : ℝ)) := by
    exact Real.log_le_log (by positivity) hcap
  have hRle : (R : ℝ) ≤ (x : ℝ) / (M : ℝ) := by
    simpa only [R] using
      (Nat.cast_div_le (α := ℝ) (m := x) (n := M))
  have hxm : 0 ≤ (x : ℝ) / (M : ℝ) := by positivity
  have hsqrtR : Real.sqrt (R : ℝ) ≤
      Real.sqrt ((x : ℝ) / (M : ℝ)) := Real.sqrt_le_sqrt hRle
  have hsqrtAddM :
      Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) ≤
        Real.sqrt (M : ℝ) + (Q : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hcross : 0 ≤ (Q : ℝ) * Real.sqrt (M : ℝ) := by positivity
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg M),
        Real.sqrt_nonneg (M : ℝ)]
  have hsqrtAddR :
      Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) ≤
        Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ) := by
    calc
      Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) ≤
          Real.sqrt (R : ℝ) + (Q : ℝ) := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · have hcross : 0 ≤ (Q : ℝ) * Real.sqrt (R : ℝ) := by positivity
          nlinarith [Real.sq_sqrt (Nat.cast_nonneg R),
            Real.sqrt_nonneg (R : ℝ)]
      _ ≤ Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ) := by
        simpa only [add_comm] using add_le_add_right hsqrtR (Q : ℝ)
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlogX : 0 ≤ Real.log (4 * (x : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 4 * x by omega))
  have hlogK : 0 ≤
      Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) :=
    Real.log_nonneg (by
      have hKpos : 0 < (M + M) * R := Nat.mul_pos (by omega) hR
      exact_mod_cast (show 1 ≤ 2 * ((M + M) * R) by omega))
  have hstage :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi) ≤
        akbaryHambrookC3 *
          (Real.sqrt (M : ℝ) + (Q : ℝ)) *
          (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
          Real.sqrt (M : ℝ) *
          Real.sqrt ((x : ℝ) / (M : ℝ)) *
          Real.log (2 * (M : ℝ)) * Real.log (4 * (x : ℝ)) := by
    calc
      _ ≤ akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          (Real.sqrt (M : ℝ) * Real.log (2 * (M : ℝ))) *
          Real.sqrt (R : ℝ) *
          Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) := by
        exact hraw.trans (by
          gcongr
          positivity [akbaryHambrookC3_pos])
      _ ≤ akbaryHambrookC3 *
          (Real.sqrt (M : ℝ) + (Q : ℝ)) *
          (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
          (Real.sqrt (M : ℝ) * Real.log (2 * (M : ℝ))) *
          Real.sqrt ((x : ℝ) / (M : ℝ)) *
          Real.log (4 * (x : ℝ)) := by
        gcongr <;> positivity [akbaryHambrookC3_pos]
      _ = akbaryHambrookC3 *
          (Real.sqrt (M : ℝ) + (Q : ℝ)) *
          (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
          Real.sqrt (M : ℝ) *
          Real.sqrt ((x : ℝ) / (M : ℝ)) *
          Real.log (2 * (M : ℝ)) * Real.log (4 * (x : ℝ)) := by ring
  have hmReal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt hmReal.le
  have hmx : (M : ℝ) * ((x : ℝ) / (M : ℝ)) = (x : ℝ) := by
    field_simp
  have hprod : Real.sqrt (M : ℝ) *
      Real.sqrt ((x : ℝ) / (M : ℝ)) = Real.sqrt (x : ℝ) := by
    rw [← Real.sqrt_mul hmReal.le, hmx]
  have hsR : Real.sqrt ((x : ℝ) / (M : ℝ)) *
      Real.sqrt ((x : ℝ) / (M : ℝ)) = (x : ℝ) / (M : ℝ) :=
    Real.mul_self_sqrt hxm
  have hsX : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqrtXM : Real.sqrt ((x : ℝ) * (M : ℝ)) =
      Real.sqrt (x : ℝ) * Real.sqrt (M : ℝ) :=
    Real.sqrt_mul (by positivity) _
  have hsqrtMne : Real.sqrt (M : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hmReal
  have hdiv : (x : ℝ) / Real.sqrt (M : ℝ) =
      ((x : ℝ) / (M : ℝ)) * Real.sqrt (M : ℝ) := by
    field_simp
    nlinarith
  have hmul : (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ)) =
      Real.sqrt (x : ℝ) * Real.sqrt (M : ℝ) := by
    calc
      (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ)) =
          (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) *
            Real.sqrt ((x : ℝ) / (M : ℝ)) := by rw [hsM]
      _ = Real.sqrt (M : ℝ) *
          (Real.sqrt (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ))) := by ring
      _ = Real.sqrt (M : ℝ) * Real.sqrt (x : ℝ) := by rw [hprod]
      _ = Real.sqrt (x : ℝ) * Real.sqrt (M : ℝ) := mul_comm _ _
  have hscalar :
      (Real.sqrt (M : ℝ) + (Q : ℝ)) *
          (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
          Real.sqrt (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ)) =
        (x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
          (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) := by
    calc
      _ = (Real.sqrt (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ))) *
            (Real.sqrt (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ))) +
          (Q : ℝ) * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) *
            Real.sqrt ((x : ℝ) / (M : ℝ)) +
          (Q : ℝ) * (Real.sqrt ((x : ℝ) / (M : ℝ)) *
            Real.sqrt ((x : ℝ) / (M : ℝ))) * Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 *
            (Real.sqrt (M : ℝ) * Real.sqrt ((x : ℝ) / (M : ℝ))) := by ring
      _ = (x : ℝ) + (Q : ℝ) * (M : ℝ) *
            Real.sqrt ((x : ℝ) / (M : ℝ)) +
          (Q : ℝ) * ((x : ℝ) / (M : ℝ)) * Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) := by
        rw [hprod, hsX, hsM, hsR]
      _ = (x : ℝ) + (Q : ℝ) *
            (Real.sqrt (x : ℝ) * Real.sqrt (M : ℝ)) +
          (Q : ℝ) * ((x : ℝ) / Real.sqrt (M : ℝ)) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) := by
        rw [mul_assoc (Q : ℝ) (M : ℝ), hmul,
          mul_assoc (Q : ℝ) ((x : ℝ) / (M : ℝ)), ← hdiv]
      _ = _ := by rw [hsqrtXM]; ring
  calc
    _ ≤ akbaryHambrookC3 *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
          (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        Real.log (2 * (M : ℝ)) * Real.log (4 * (x : ℝ)) := by
      rw [← hscalar]
      simpa only [mul_assoc] using hstage
    _ = _ := by rfl

end

end BoundedGaps.Maynard
