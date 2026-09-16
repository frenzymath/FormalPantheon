import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletProgressionError

/-!
# Log-power errors for decimal-smooth progressions

This derives the project-required two-exponent specialization of
`MONTGOMERY-VAUGHAN-MNT-I`, Corollary 11.19, pp. 380--381, from the stronger
decimal-smooth exponential estimate.
-/

open Filter

namespace PrimesRestrictedDigits

/-- Every fixed natural power of `log x` is eventually bounded by a
coefficient-one square-root-logarithmic exponential. -/
theorem eventually_log_pow_le_exp_sqrt_log
    {d : Real} (hd : 0 < d) (N : Nat) :
    ∀ᶠ x : Real in atTop,
      Real.log x ^ N <=
        Real.exp (d * Real.sqrt (Real.log x)) := by
  let n : Nat := 2 * N
  let e : Real := d / 2
  let F : Real := (n.factorial : Real) / e ^ n
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hRoot :
      Tendsto (fun x : Real => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hScaled :
      Tendsto (fun x : Real => e * Real.sqrt (Real.log x)) atTop atTop :=
    hRoot.const_mul_atTop he
  have hExp :
      Tendsto
        (fun x : Real => Real.exp (e * Real.sqrt (Real.log x)))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hScaled
  have hFixed := hExp.eventually_ge_atTop F
  filter_upwards [hFixed, eventually_ge_atTop (1 : Real)] with x hFixedX hx
  let ell : Real := Real.log x
  let s : Real := Real.sqrt ell
  let z : Real := e * s
  have hEllNonneg : 0 <= ell := by
    dsimp [ell]
    exact Real.log_nonneg hx
  have hsNonneg : 0 <= s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hsSq : s ^ 2 = ell := by
    dsimp [s]
    exact Real.sq_sqrt hEllNonneg
  have hzNonneg : 0 <= z := by
    dsimp [z]
    positivity
  have hFactorialPos : (0 : Real) < n.factorial := by
    exact_mod_cast Nat.factorial_pos n
  have hePowPos : 0 < e ^ n := pow_pos he n
  have hSeries := Real.pow_div_factorial_le_exp z hzNonneg n
  have hPoly : s ^ n <= F * Real.exp z := by
    calc
      s ^ n = F * (z ^ n / (n.factorial : Real)) := by
        dsimp [F, z]
        field_simp [hFactorialPos.ne', hePowPos.ne']
        ring
      _ <= F * Real.exp z :=
        mul_le_mul_of_nonneg_left hSeries (by positivity)
  have hFixedX' : F <= Real.exp z := by
    simpa only [z, s, ell] using hFixedX
  calc
    Real.log x ^ N = ell ^ N := by rfl
    _ = (s ^ 2) ^ N := by rw [hsSq]
    _ = s ^ (2 * N) := (pow_mul s 2 N).symm
    _ = s ^ n := by rfl
    _ <= F * Real.exp z := hPoly
    _ <= Real.exp z * Real.exp z :=
      mul_le_mul_of_nonneg_right hFixedX' (Real.exp_pos _).le
    _ = Real.exp (d * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [z, e, s, ell]
      ring

/-- For independent natural error and modulus exponents, decimal-smooth
progression sums satisfy the project-required eventual log-power bound. -/
theorem exists_abs_vonMangoldtProgressionSum_sub_main_log_pow_le
    (H B : Nat) :
    ∃ C x0 : Real,
      0 < C ∧ 4 <= x0 ∧
      ∀ x : Real,
        x0 <= x ->
        ∀ q : Nat,
          0 < q -> IsDecimalSmooth q ->
          ∀ a : Nat,
            Nat.Coprime a q ->
            (q : Real) <= Real.log x ^ B ->
            abs (vonMangoldtProgressionSum q a x -
              x / (q.totient : Real)) <=
                C * x / Real.log x ^ H := by
  obtain ⟨d, M, L0, hd, hM, hL0, hExpError⟩ :=
    exists_abs_vonMangoldtProgressionSum_sub_main_exp_sqrt_log_le
  have hModulusEvent := eventually_log_pow_le_exp_sqrt_log
    (d := 2 * d) (mul_pos (by norm_num) hd) B
  have hErrorEvent := eventually_log_pow_le_exp_sqrt_log hd H
  obtain ⟨XB, hXB⟩ := eventually_atTop.mp hModulusEvent
  obtain ⟨XH, hXH⟩ := eventually_atTop.mp hErrorEvent
  let x0 : Real := max 4 (max (Real.exp L0) (max XB XH))
  have hx0Four : 4 <= x0 := le_max_left _ _
  have hCutoffX0 : Real.exp L0 <= x0 :=
    (le_max_left (Real.exp L0) (max XB XH)).trans (le_max_right 4 _)
  have hXBX0 : XB <= x0 :=
    (le_max_left XB XH).trans
      ((le_max_right (Real.exp L0) (max XB XH)).trans (le_max_right 4 _))
  have hXHX0 : XH <= x0 :=
    (le_max_right XB XH).trans
      ((le_max_right (Real.exp L0) (max XB XH)).trans (le_max_right 4 _))
  refine ⟨M, x0, hM, hx0Four, ?_⟩
  intro x hx q hq hSmooth a ha hqLog
  have hxFour : 4 <= x := hx0Four.trans hx
  have hxPos : 0 < x := by linarith
  have hxCutoff : Real.exp L0 <= x := hCutoffX0.trans hx
  have hModulus :
      Real.log x ^ B <=
        Real.exp (2 * d * Real.sqrt (Real.log x)) :=
    hXB x (hXBX0.trans hx)
  have hErrorScale :
      Real.log x ^ H <=
        Real.exp (d * Real.sqrt (Real.log x)) :=
    hXH x (hXHX0.trans hx)
  have hExpBound := hExpError q hq hSmooth a ha x hxCutoff
    (hqLog.trans hModulus)
  have hLogPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLogPowPos : 0 < Real.log x ^ H := pow_pos hLogPos H
  have hNumeratorNonneg : 0 <= M * x := by positivity
  calc
    abs (vonMangoldtProgressionSum q a x -
        x / (q.totient : Real)) <=
        M * x / Real.exp (d * Real.sqrt (Real.log x)) := hExpBound
    _ <= M * x / Real.log x ^ H := by
      rw [div_le_div_iff₀ (Real.exp_pos _) hLogPowPos]
      exact mul_le_mul_of_nonneg_left hErrorScale hNumeratorNonneg

end PrimesRestrictedDigits
