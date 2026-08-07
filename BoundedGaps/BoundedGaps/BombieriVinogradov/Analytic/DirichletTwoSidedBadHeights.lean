import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorSupport
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProductZeroOrdinates

/-!
# Two-sided bad heights for a Dirichlet contour

This file combines primitive-inducer or regularized-zeta divisor ordinates
with inducing-product zero ordinates at both horizontal signs. It only builds
and counts the finite forbidden-height inventory; height selection is a
separate successor.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86 and
110--115. The two-sign arbitrary-character count is project-derived.
Semantic review: `SEM-511`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

private local instance characterDecidableEq (q : ℕ) :
    DecidableEq (DirichletCharacter ℂ q) :=
  Classical.decEq _

/-- Ordinates from the primitive-inducer or regularized-zeta divisor disk. -/
noncomputable def characterBaseDivisorOrdinatesInLocalDisk
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : Set ℝ :=
  if chi = 1 then
    Complex.im ''
      (MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 3)).support
  else
    Complex.im ''
      (MeromorphicOn.divisor
        (DirichletCharacter.LFunction chi.primitiveCharacter)
        (closedBall ((2 : ℂ) + t * I) 6)).support

/-- Base analytic and inducing-product bad ordinates near one signed center. -/
noncomputable def dirichletLocalBadOrdinates
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : Set ℝ :=
  characterBaseDivisorOrdinatesInLocalDisk chi t ∪
    inducingEulerProductZeroOrdinatesInUnitWindow chi t

/-- A two-sided over-approximation of candidate contour heights to avoid. -/
noncomputable def dirichletTwoSidedBadHeights
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) : Set ℝ :=
  let m := T + 1 / 2
  dirichletLocalBadOrdinates chi m ∪
    (fun gamma : ℝ => -gamma) '' dirichletLocalBadOrdinates chi (-m)

private theorem primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

private theorem characterBaseDivisorOrdinatesInLocalDisk_finite
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    (characterBaseDivisorOrdinatesInLocalDisk chi t).Finite := by
  rw [characterBaseDivisorOrdinatesInLocalDisk]
  split_ifs with hchi
  · apply Set.Finite.image
    have hA : AnalyticOnNhd ℂ riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 3) :=
      fun z _ => differentiable_riemannZeta₁.analyticAt z
    exact hA.meromorphicOn.divisor_support_finite_of_subset
      (isCompact_closedBall ((2 : ℂ) + t * I) 3) Set.Subset.rfl
  · exact Set.Finite.image Complex.im
      (divisor_LFunction_closedBall_support_finite
        (primitiveCharacter_ne_one_of_ne_one chi hchi)
        ((2 : ℂ) + t * I) 6)

private theorem dirichletLocalBadOrdinates_finite
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    (dirichletLocalBadOrdinates chi t).Finite :=
  (characterBaseDivisorOrdinatesInLocalDisk_finite chi t).union
    (inducingEulerProductZeroOrdinatesInUnitWindow_finite chi t)

/-- The two-sided forbidden-height inventory is finite. -/
theorem dirichletTwoSidedBadHeights_finite
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) :
    (dirichletTwoSidedBadHeights chi T).Finite := by
  rw [dirichletTwoSidedBadHeights]
  exact (dirichletLocalBadOrdinates_finite chi (T + 1 / 2)).union
    ((dirichletLocalBadOrdinates_finite chi (-(T + 1 / 2))).image
      (fun gamma : ℝ => -gamma))

private theorem cast_ncard_union_le (s t : Set ℝ) :
    ((s ∪ t).ncard : ℝ) ≤ (s.ncard : ℝ) + (t.ncard : ℝ) := by
  exact_mod_cast Set.ncard_union_le s t

private theorem log_midpoint_scale_le_two_mul
    {q : ℕ} [NeZero q]
    (r : ℝ) (hr : 0 < r) (hrq : r ≤ (q : ℝ))
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log (r * (|T + 1 / 2| + 2)) ≤
      2 * Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans hq
  have hm : 0 ≤ T + 1 / 2 := by linarith
  have harg : 0 < r * (|T + 1 / 2| + 2) := by positivity
  have hle : r * (|T + 1 / 2| + 2) ≤
      ((q : ℝ) * (T + 2)) ^ 2 := by
    rw [abs_of_nonneg hm]
    have hmid : T + 1 / 2 + 2 ≤ (T + 2) ^ 2 := by
      nlinarith [sq_nonneg T]
    have hqq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
    calc
      r * (T + 1 / 2 + 2) ≤ (q : ℝ) * (T + 1 / 2 + 2) :=
        mul_le_mul_of_nonneg_right hrq (by linarith)
      _ ≤ (q : ℝ) * (T + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hmid hq0
      _ ≤ (q : ℝ) ^ 2 * (T + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hqq (sq_nonneg (T + 2))
      _ = ((q : ℝ) * (T + 2)) ^ 2 := by ring
  calc
    Real.log (r * (|T + 1 / 2| + 2)) ≤
        Real.log (((q : ℝ) * (T + 2)) ^ 2) :=
      Real.log_le_log harg hle
    _ = 2 * Real.log ((q : ℝ) * (T + 2)) := by
      rw [Real.log_pow]
      norm_num

private theorem log_level_le_log_heightScale
    {q : ℕ} [NeZero q]
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply Real.log_le_log hq
  nlinarith [mul_nonneg hq.le (show 0 ≤ T + 1 by linarith)]

private theorem cast_ncard_localBadOrdinates_le
    {AL AZ A : ℕ}
    (hAL : 37 ≤ AL)
    (hprimitive :
      ∀ (d : ℕ) [NeZero d], 1 < d →
        ∀ (psi : DirichletCharacter ℂ d), psi.IsPrimitive →
          ∀ t : ℝ,
            ((MeromorphicOn.divisor
                (DirichletCharacter.LFunction psi)
                (closedBall ((2 : ℂ) + t * I) 6)).support.ncard : ℝ) ≤
              2 * (AL : ℝ) *
                Real.log ((d : ℝ) * (|t| + 2)))
    (hzeta :
      ∀ t : ℝ,
        ((MeromorphicOn.divisor riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) ≤
          12 * (AZ : ℝ) * Real.log (|t| + 2))
    (hALA : AL ≤ A) (hAZA : AZ ≤ A)
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T t : ℝ)
    (hT : 2 ≤ T) (ht : |t| = T + 1 / 2) :
    ((dirichletLocalBadOrdinates chi t).ncard : ℝ) ≤
      36 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
  let L := Real.log ((q : ℝ) * (T + 2))
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLpos : 0 < L := by
    apply Real.log_pos
    nlinarith [mul_le_mul_of_nonneg_left
      (show (4 : ℝ) ≤ T + 2 by linarith) (show (0 : ℝ) ≤ q by positivity)]
  have hAone : 1 ≤ A := hAL.trans hALA |>.trans' (by omega)
  have hproduct :
      ((inducingEulerProductZeroOrdinatesInUnitWindow chi t).ncard : ℝ) ≤
        12 * (A : ℝ) * L := by
    calc
      ((inducingEulerProductZeroOrdinatesInUnitWindow chi t).ncard : ℝ) ≤
          12 * Real.log (q : ℝ) :=
        ncard_inducingEulerProductZeroOrdinatesInUnitWindow_le chi t
      _ ≤ 12 * L := by
        exact mul_le_mul_of_nonneg_left
          (log_level_le_log_heightScale T hT) (by norm_num)
      _ ≤ 12 * (A : ℝ) * L := by
        have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hAone
        nlinarith [mul_le_mul_of_nonneg_right hAreal hLpos.le]
  have hbase :
      ((characterBaseDivisorOrdinatesInLocalDisk chi t).ncard : ℝ) ≤
        24 * (A : ℝ) * L := by
    rw [characterBaseDivisorOrdinatesInLocalDisk]
    split_ifs with hchi
    · let S := (MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 3)).support
      have hSfinite : S.Finite := by
        have hAnalytic : AnalyticOnNhd ℂ riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 3) :=
          fun z _ => differentiable_riemannZeta₁.analyticAt z
        exact hAnalytic.meromorphicOn.divisor_support_finite_of_subset
          (isCompact_closedBall ((2 : ℂ) + t * I) 3) Set.Subset.rfl
      have himage : ((Complex.im '' S).ncard : ℝ) ≤ (S.ncard : ℝ) := by
        exact_mod_cast Set.ncard_image_le hSfinite
      have hlog : Real.log (|t| + 2) ≤ 2 * L := by
        rw [ht]
        have hscale :=
          log_midpoint_scale_le_two_mul (q := q) 1 (by norm_num) hq T hT
        rw [abs_of_nonneg (show 0 ≤ T + 1 / 2 by linarith)] at hscale
        simpa [L] using hscale
      have hAZreal : (AZ : ℝ) ≤ A := by exact_mod_cast hAZA
      calc
        ((Complex.im '' S).ncard : ℝ) ≤ (S.ncard : ℝ) := himage
        _ ≤ 12 * (AZ : ℝ) * Real.log (|t| + 2) := by
          simpa [S] using hzeta t
        _ ≤ 24 * (A : ℝ) * L := by
          have hlogNonneg : 0 ≤ Real.log (|t| + 2) := by
            apply Real.log_nonneg
            linarith [abs_nonneg t]
          nlinarith [mul_le_mul hAZreal hlog hlogNonneg
            (by positivity : (0 : ℝ) ≤ A)]
    · let d := chi.conductor
      letI : NeZero d := ⟨chi.conductor_ne_zero⟩
      have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      have hdne : d ≠ 1 := by
        intro hd
        exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
      have hd : 1 < d := by omega
      let S := (MeromorphicOn.divisor
          (DirichletCharacter.LFunction chi.primitiveCharacter)
          (closedBall ((2 : ℂ) + t * I) 6)).support
      have hpsi : chi.primitiveCharacter ≠ 1 :=
        primitiveCharacter_ne_one_of_ne_one chi hchi
      have hSfinite : S.Finite := by
        simpa [S] using divisor_LFunction_closedBall_support_finite hpsi
          ((2 : ℂ) + t * I) 6
      have himage : ((Complex.im '' S).ncard : ℝ) ≤ (S.ncard : ℝ) := by
        exact_mod_cast Set.ncard_image_le hSfinite
      have hdqNat : d ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
          chi.conductor_dvd_level
      have hdq : (d : ℝ) ≤ q := by exact_mod_cast hdqNat
      have hlog : Real.log ((d : ℝ) * (|t| + 2)) ≤ 2 * L := by
        rw [ht]
        have hscale := log_midpoint_scale_le_two_mul (q := q)
          (d : ℝ) (by exact_mod_cast hdpos) hdq T hT
        rw [abs_of_nonneg (show 0 ≤ T + 1 / 2 by linarith)] at hscale
        simpa [L] using hscale
      have hALreal : (AL : ℝ) ≤ A := by exact_mod_cast hALA
      calc
        ((Complex.im '' S).ncard : ℝ) ≤ (S.ncard : ℝ) := himage
        _ ≤ 2 * (AL : ℝ) * Real.log ((d : ℝ) * (|t| + 2)) := by
          simpa [S, d] using hprimitive d hd chi.primitiveCharacter
            chi.primitiveCharacter_isPrimitive t
        _ ≤ 24 * (A : ℝ) * L := by
          have hlogNonneg :
              0 ≤ Real.log ((d : ℝ) * (|t| + 2)) := by
            apply Real.log_nonneg
            have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd.le
            nlinarith [mul_le_mul_of_nonneg_left
              (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
              (by positivity : (0 : ℝ) ≤ d)]
          nlinarith [mul_le_mul hALreal hlog hlogNonneg
            (by positivity : (0 : ℝ) ≤ A)]
  have hunion := cast_ncard_union_le
    (characterBaseDivisorOrdinatesInLocalDisk chi t)
    (inducingEulerProductZeroOrdinatesInUnitWindow chi t)
  rw [← dirichletLocalBadOrdinates] at hunion
  nlinarith

/-- One absolute constant bounds every two-sided forbidden-height inventory. -/
theorem exists_nat_ncard_dirichletTwoSidedBadHeights_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (T : ℝ),
          2 ≤ T →
            ((dirichletTwoSidedBadHeights chi T).ncard : ℝ) ≤
              72 * (A : ℝ) *
                Real.log ((q : ℝ) * (T + 2)) := by
  obtain ⟨AL, hAL, hprimitive⟩ :=
    exists_nat_ncard_support_divisor_LFunction_radiusSix_le
  obtain ⟨AZ, _, hzeta⟩ :=
    exists_nat_ncard_support_divisor_riemannZeta₁_radiusThree_le
  let A := max AL AZ
  refine ⟨A, hAL.trans (Nat.le_max_left AL AZ), ?_⟩
  intro q _ chi T hT
  let m := T + 1 / 2
  let P := dirichletLocalBadOrdinates chi m
  let N := dirichletLocalBadOrdinates chi (-m)
  have hP : (P.ncard : ℝ) ≤
      36 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
    apply cast_ncard_localBadOrdinates_le hAL hprimitive hzeta
      (Nat.le_max_left AL AZ) (Nat.le_max_right AL AZ) chi T m hT
    change |T + 1 / 2| = T + 1 / 2
    rw [abs_of_nonneg (by linarith)]
  have hN : (N.ncard : ℝ) ≤
      36 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
    apply cast_ncard_localBadOrdinates_le hAL hprimitive hzeta
      (Nat.le_max_left AL AZ) (Nat.le_max_right AL AZ) chi T (-m) hT
    change |-(T + 1 / 2)| = T + 1 / 2
    rw [abs_neg, abs_of_nonneg (by linarith)]
  have hneg :
      ((((fun gamma : ℝ => -gamma) '' N).ncard : ℕ) : ℝ) =
        (N.ncard : ℝ) := by
    rw [Set.ncard_image_of_injective N]
    intro x y hxy
    linarith
  have hunion := cast_ncard_union_le P ((fun gamma : ℝ => -gamma) '' N)
  rw [hneg] at hunion
  change ((dirichletTwoSidedBadHeights chi T).ncard : ℝ) ≤ _
  simpa [dirichletTwoSidedBadHeights, m, P, N] using
    hunion.trans (by linarith)

end

end BoundedGaps.Maynard
