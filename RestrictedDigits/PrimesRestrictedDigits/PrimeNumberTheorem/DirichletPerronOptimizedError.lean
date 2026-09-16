import PrimesRestrictedDigits.BasicEstimates.PrimeRemainderDecay
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronError
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronOptimizedPower

/-!
# Exponential Dirichlet character error for decimal-smooth levels

This implements the no-exceptional-zero branch of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16 and Eq. (11.23),
pp. 378--379, for the project's decimal-smooth modulus family.
-/

namespace PrimesRestrictedDigits

/-- There are common square-root-logarithmic decay constants for the
nonprincipal and principal twisted von Mangoldt sums at every decimal-smooth
level in the source's height range. -/
theorem exists_norm_dirichletVonMangoldtSum_exp_sqrt_log_branches_le :
    ∃ d M L0 : Real,
      0 < d ∧ 0 < M ∧ Real.log 4 <= L0 ∧
      (∀ {q : Nat} [NeZero q]
          (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q -> chi ≠ 1 ->
        ∀ x : Real,
          Real.exp L0 <= x ->
          (q : Real) <=
            Real.exp (2 * d * Real.sqrt (Real.log x)) ->
          norm (dirichletVonMangoldtSum chi x) <=
            M * x /
              Real.exp (d * Real.sqrt (Real.log x))) ∧
      (∀ {q : Nat} [NeZero q],
        IsDecimalSmooth q ->
        ∀ x : Real,
          Real.exp L0 <= x ->
          (q : Real) <=
            Real.exp (2 * d * Real.sqrt (Real.log x)) ->
          norm (dirichletVonMangoldtSum
              (1 : DirichletCharacter Complex q) x - (x : Complex)) <=
            M * x /
              Real.exp (d * Real.sqrt (Real.log x))) := by
  obtain ⟨c, K, hc, hK, hNonprincipal, hPrincipal⟩ :=
    exists_norm_dirichletVonMangoldtSum_source_branches_le
  let d : Real := dirichletPerronDecay c
  let M : Real := 48 * K / d ^ 4
  let L0 : Real := max (Real.log 4) (dirichletPerronLogThreshold c)
  have hd : 0 < d := by
    dsimp [d]
    exact dirichletPerronDecay_pos hc.1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hOptimize :
      ∀ {q : Nat} [NeZero q] (z : Complex) (x : Real),
        Real.exp L0 <= x ->
        (q : Real) <=
          Real.exp (2 * d * Real.sqrt (Real.log x)) ->
        (∀ T : Real,
          4 <= x -> 2 <= T -> T <= x -> (q : Real) <= x ->
          norm z <=
            K * x * Real.log x ^ 2 *
              (1 / T + Real.exp
                (-c * Real.log x /
                  (5 * Real.log ((q : Real) * (T + 4)))))) ->
        norm z <=
          M * x / Real.exp (d * Real.sqrt (Real.log x)) := by
    intro q inst z x hxCutoff hq hRaw
    let ell : Real := Real.log x
    let s : Real := Real.sqrt ell
    let T : Real := dirichletPerronHeight c x
    let F : Real := Real.exp
      (-c * ell / (5 * Real.log ((q : Real) * (T + 4))))
    have hxPos : 0 < x := (Real.exp_pos L0).trans_le hxCutoff
    have hL0Log : L0 <= Real.log x :=
      (Real.le_log_iff_exp_le hxPos).2 hxCutoff
    have hxFour : 4 <= x := by
      calc
        (4 : Real) = Real.exp (Real.log 4) :=
          (Real.exp_log (by norm_num)).symm
        _ <= Real.exp L0 :=
          Real.exp_le_exp.mpr (le_max_left _ _)
        _ <= x := hxCutoff
    have hLarge : dirichletPerronLogThreshold c <= Real.log x :=
      (le_max_right (Real.log 4) (dirichletPerronLogThreshold c)).trans hL0Log
    have hTBounds : 4 <= T ∧ T <= x := by
      dsimp [T]
      exact dirichletPerronHeight_bounds hc hxPos hLarge
    have hTTwo : 2 <= T := by linarith [hTBounds.1]
    have hTPos : 0 < T := by linarith [hTBounds.1]
    have hHeight :
        T = Real.exp (2 * d * s) := by
      dsimp [T, d, s, ell]
      exact dirichletPerronHeight_eq_exp_two_mul_decay_sqrt_log
    have hqT : (q : Real) <= T := by
      rw [hHeight]
      exact hq
    have hqx : (q : Real) <= x := hqT.trans hTBounds.2
    have hFactor : F <= 1 / T := by
      dsimp [F, T, ell]
      exact dirichletPerronDecayFactor_le_inv_height hc hxPos hLarge hqT
    have hParen : 1 / T + F <= 2 / T := by
      calc
        1 / T + F <= 1 / T + 1 / T := add_le_add_right hFactor _
        _ = 2 / T := by ring
    have hBaseNonneg : 0 <= K * x * ell ^ 2 := by
      positivity
    have hRawBound := hRaw T hxFour hTTwo hTBounds.2 hqx
    have hFirst : norm z <= 2 * K * x * ell ^ 2 / T := by
      calc
        norm z <= K * x * ell ^ 2 * (1 / T + F) := by
          simpa only [ell, T, F] using hRawBound
        _ <= K * x * ell ^ 2 * (2 / T) :=
          mul_le_mul_of_nonneg_left hParen hBaseNonneg
        _ = 2 * K * x * ell ^ 2 / T := by ring
    have hxOne : 1 <= x := by linarith [hxFour]
    have hScale := log_sq_le_exp_sqrt_log_scale
      (c := d) (x := x) hd hxOne
    have hMultiplierNonneg : 0 <= 2 * K * x / T := by
      positivity
    have hScaled :=
      mul_le_mul_of_nonneg_left hScale hMultiplierNonneg
    have hExpTwo :
        Real.exp (2 * d * s) =
          Real.exp (d * s) * Real.exp (d * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      norm z <= (2 * K * x / T) * ell ^ 2 := by
        calc
          norm z <= 2 * K * x * ell ^ 2 / T := hFirst
          _ = (2 * K * x / T) * ell ^ 2 := by ring
      _ <= (2 * K * x / T) *
          (24 / d ^ 4 * Real.exp (d * s)) := by
        simpa only [ell, s] using hScaled
      _ = M * x / Real.exp (d * s) := by
        rw [hHeight, hExpTwo]
        dsimp [M]
        field_simp [hd.ne', Real.exp_ne_zero]; ring
      _ = M * x / Real.exp (d * Real.sqrt (Real.log x)) := by rfl
  refine ⟨d, M, L0, hd, hM, le_max_left _ _, ?_, ?_⟩
  · intro q inst chi hq hchi x hxCutoff hqx
    apply hOptimize (z := dirichletVonMangoldtSum chi x) x hxCutoff hqx
    intro T hx hT hTx hLevel
    exact hNonprincipal chi hq hchi x T hx hT hTx hLevel
  · intro q inst hq x hxCutoff hqx
    apply hOptimize
      (z := dirichletVonMangoldtSum
        (1 : DirichletCharacter Complex q) x - (x : Complex))
      x hxCutoff hqx
    intro T hx hT hTx hLevel
    exact hPrincipal hq x T hx hT hTx hLevel

end PrimesRestrictedDigits
