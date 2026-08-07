import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamarePrefix
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermEnergy
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermMangoldtEnergy

/-!
# Vaughan's fourth-term block estimate

This file combines the maximal bilinear theorem with the von Mangoldt and
Granville--Ramare coefficient energies on one active dyadic block. It keeps a
generic proved Chebyshev constant, so the exact source constant and Mathlib's
unconditional constant remain visibly distinct.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 22--23, through equation
(6.14). Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- The square-root form of equation (6.14) on the fixed fourth-term
`k` support. -/
theorem sqrt_sum_norm_sq_vaughanFourthCoefficient_dyadic_le
    {V : ℝ} {x alpha : ℕ} (hV : 1 ≤ V) :
    Real.sqrt (∑ k ∈ vaughanFourthDyadicKIndices V x alpha,
      ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) ≤
      2 / Real.sqrt 3 *
        Real.sqrt ((x : ℝ) / ((2 ^ alpha : ℕ) : ℝ)) *
        Real.log (Real.exp 3 * V) := by
  let M : ℕ := 2 ^ alpha
  have hM : 0 < M := by positivity
  have henergy := sum_norm_sq_vaughanFourthCoefficient_Ioc_le
    (V := V) (x := x) (M := M) hV hM
  have hLog : 0 ≤ Real.log (Real.exp 3 * V) := by
    apply Real.log_nonneg
    have hExp : 1 ≤ Real.exp (3 : ℝ) :=
      (Real.one_le_exp_iff).2 (by norm_num)
    nlinarith [mul_pos (Real.exp_pos 3) (zero_lt_one.trans_le hV)]
  have hBase : 0 ≤ 4 * (x : ℝ) / (3 * (M : ℝ)) := by positivity
  have hSqrt := Real.sqrt_le_sqrt henergy
  have hBaseEq :
      4 * (x : ℝ) / (3 * (M : ℝ)) =
        (4 / 3 : ℝ) * ((x : ℝ) / (M : ℝ)) := by ring
  have hSqrtFourThirds :
      Real.sqrt (4 / 3 : ℝ) = 2 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
    have hSqrtFour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hSqrtFour]
  rw [Real.sqrt_mul hBase, Real.sqrt_sq hLog, hBaseEq,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
    hSqrtFourThirds] at hSqrt
  simpa only [vaughanFourthDyadicKIndices, M] using hSqrt

/-- The exact coefficient constant before the dyadic scale count in
Akbary--Hambrook equation (6.15). -/
noncomputable def vaughanFourthBlockConstant (A : ℝ) : ℝ :=
  2 * Real.sqrt 2 * Real.sqrt A * akbaryHambrookC3 / Real.sqrt 3

/-- Numerical maximal estimate for one active fourth-term dyadic block,
given a proved global Chebyshev constant `A`. -/
theorem sum_weighted_vaughanFourthDyadicBlockMaximum_le_of_psi
    {A U V : ℝ} {x Q alpha : ℕ}
    (hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (_hx : 1 ≤ x) (_hU : 1 ≤ U) (hV : 1 ≤ V)
    (halpha : alpha ∈ vaughanFourthDyadicExponents U V x) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanFourthDyadicBlockMaximum U V x q alpha chi) ≤
      vaughanFourthBlockConstant A *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (2 ^ alpha : ℕ)) +
          (Q : ℝ) * (x : ℝ) /
            Real.sqrt ((2 ^ alpha : ℕ) : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        Real.sqrt (Real.log (2 * ((2 ^ alpha : ℕ) : ℝ))) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) := by
  classical
  let M : ℕ := 2 ^ alpha
  let R : ℕ := x / M
  have hM : 0 < M := by positivity
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  rcases Finset.mem_filter.mp halpha with
    ⟨_halphaRange, _hMlower, hMupper⟩
  change (M : ℝ) < (x : ℝ) / V at hMupper
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hQuotientLeX : (x : ℝ) / V ≤ (x : ℝ) := by
    apply (div_le_iff₀ hVpos).2
    nlinarith [show (0 : ℝ) ≤ (x : ℝ) by positivity]
  have hMltReal : (M : ℝ) < (x : ℝ) := hMupper.trans_le hQuotientLeX
  have hMlt : M < x := by exact_mod_cast hMltReal
  have hR : 0 < R := Nat.div_pos hMlt.le hM
  have hsm : vaughanFourthDyadicMIndices U V x alpha ⊆
      Finset.Ioc M (M + M) := by
    intro m hm
    have hmBlock := (Finset.mem_filter.mp hm).1
    rw [dyadicBlock, Finset.mem_Ioc] at hmBlock
    rw [Finset.mem_Ioc]
    constructor
    · simpa only [M] using hmBlock.1
    · calc
        m ≤ 2 ^ (alpha + 1) := hmBlock.2
        _ = M + M := by
          rw [pow_succ]
          dsimp only [M]
          omega
  have hsn : vaughanFourthDyadicKIndices V x alpha ⊆
      Finset.Ioc 0 (0 + R) := by
    intro k hk
    have hkIoc := (Finset.mem_filter.mp hk).1
    rw [Finset.mem_Ioc]
    constructor
    · exact (Finset.mem_Ioc.mp hkIoc).1
    · simpa only [vaughanFourthDyadicKIndices, R, M, zero_add] using
        (Finset.mem_Ioc.mp hkIoc).2
  have hblock :=
    sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
      Q M M 0 R hM hR
      (vaughanFourthDyadicMIndices U V x alpha)
      (vaughanFourthDyadicKIndices V x alpha)
      hsm hsn
      (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
      (fun k ↦ (vaughanFourthCoefficient V k : ℂ))
  have hraw :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi) ≤
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
            ‖(ArithmeticFunction.vonMangoldt m : ℂ)‖ ^ 2) *
          Real.sqrt (∑ k ∈ vaughanFourthDyadicKIndices V x alpha,
            ‖(vaughanFourthCoefficient V k : ℂ)‖ ^ 2) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
    simpa only [vaughanFourthDyadicBlockMaximum, M, R, zero_add] using hblock
  have hmEnergy :=
    sqrt_sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le_of_psi
      (A := A) (U := U) (V := V) hA hpsi x alpha
  have hkEnergy :=
    sqrt_sum_norm_sq_vaughanFourthCoefficient_dyadic_le
      (V := V) (x := x) (alpha := alpha) hV
  have hMRNat : M * R ≤ x := by
    simpa only [R, Nat.mul_comm] using Nat.div_mul_le_self x M
  have hMR : (M : ℝ) * (R : ℝ) ≤ (x : ℝ) := by exact_mod_cast hMRNat
  have hcap :
      2 * ((((M + M) * R : ℕ) : ℝ)) ≤ 4 * (x : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add]
    nlinarith
  have hlogCap :
      Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) ≤
        Real.log (4 * (x : ℝ)) :=
    Real.log_le_log (by positivity) hcap
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
  have hLogM : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hLogV : 0 ≤ Real.log (Real.exp 3 * V) := by
    apply Real.log_nonneg
    have hExp : 1 ≤ Real.exp (3 : ℝ) :=
      (Real.one_le_exp_iff).2 (by norm_num)
    nlinarith [mul_pos (Real.exp_pos 3) hVpos]
  have hLogX : 0 ≤ Real.log (4 * (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * x by omega))
  have hLogK : 0 ≤
      Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) :=
    Real.log_nonneg (by
      have hKpos : 0 < (M + M) * R := Nat.mul_pos (by omega) hR
      exact_mod_cast (show 1 ≤ 2 * ((M + M) * R) by omega))
  have hstage :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi) ≤
        akbaryHambrookC3 *
          (Real.sqrt (M : ℝ) + (Q : ℝ)) *
          (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
          (Real.sqrt 2 * Real.sqrt A * Real.sqrt (M : ℝ) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) *
          (2 / Real.sqrt 3 *
            Real.sqrt ((x : ℝ) / (M : ℝ)) *
            Real.log (Real.exp 3 * V)) *
          Real.log (4 * (x : ℝ)) := by
    calc
      _ ≤ akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          (Real.sqrt 2 * Real.sqrt A * Real.sqrt (M : ℝ) *
            Real.sqrt (Real.log (2 * (M : ℝ)))) *
          (2 / Real.sqrt 3 *
            Real.sqrt ((x : ℝ) / (M : ℝ)) *
            Real.log (Real.exp 3 * V)) *
          Real.log (2 * ((((M + M) * R : ℕ) : ℝ))) := by
        exact hraw.trans (by
          gcongr
          all_goals positivity [akbaryHambrookC3_pos])
      _ ≤ _ := by
        gcongr <;> positivity [akbaryHambrookC3_pos]
  have hsM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt hMReal.le
  have hmx : (M : ℝ) * ((x : ℝ) / (M : ℝ)) = (x : ℝ) := by
    field_simp
  have hprod : Real.sqrt (M : ℝ) *
      Real.sqrt ((x : ℝ) / (M : ℝ)) = Real.sqrt (x : ℝ) := by
    rw [← Real.sqrt_mul hMReal.le, hmx]
  have hsR : Real.sqrt ((x : ℝ) / (M : ℝ)) *
      Real.sqrt ((x : ℝ) / (M : ℝ)) = (x : ℝ) / (M : ℝ) :=
    Real.mul_self_sqrt hxm
  have hsX : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqrtXM : Real.sqrt ((x : ℝ) * (M : ℝ)) =
      Real.sqrt (x : ℝ) * Real.sqrt (M : ℝ) :=
    Real.sqrt_mul (by positivity) _
  have hsqrtMne : Real.sqrt (M : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hMReal
  have hdiv : (x : ℝ) / Real.sqrt (M : ℝ) =
      ((x : ℝ) / (M : ℝ)) * Real.sqrt (M : ℝ) := by
    symm
    calc
      ((x : ℝ) / (M : ℝ)) * Real.sqrt (M : ℝ) =
          (x : ℝ) * Real.sqrt (M : ℝ) / (M : ℝ) := by ring
      _ = (x : ℝ) * Real.sqrt (M : ℝ) /
          (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) := by rw [hsM]
      _ = (x : ℝ) / Real.sqrt (M : ℝ) := by field_simp
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
        (Real.sqrt (M : ℝ) + (Q : ℝ)) *
        (Real.sqrt ((x : ℝ) / (M : ℝ)) + (Q : ℝ)) *
        (Real.sqrt 2 * Real.sqrt A * Real.sqrt (M : ℝ) *
          Real.sqrt (Real.log (2 * (M : ℝ)))) *
        (2 / Real.sqrt 3 *
          Real.sqrt ((x : ℝ) / (M : ℝ)) *
          Real.log (Real.exp 3 * V)) *
        Real.log (4 * (x : ℝ)) := hstage
    _ = vaughanFourthBlockConstant A *
        ((x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
          (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        Real.sqrt (Real.log (2 * (M : ℝ))) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) := by
      rw [← hscalar]
      unfold vaughanFourthBlockConstant
      ring
    _ = _ := by rfl

end

end BoundedGaps.Maynard
