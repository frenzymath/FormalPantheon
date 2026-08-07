import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorReciprocalBound
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedDisk

/-!
# Primitive nonprincipal horizontal logarithmic derivatives

This file combines the primitive radius-six ordinary-divisor estimate with a
two-sided selected-height clearance. It bounds the full logarithmic derivative
on both shallow horizontal lines while preserving the selected contour height.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86,
90--92, and 114--115, especially Lemmas 8.2 and 11.4 and Theorem 11.3. The
last paragraph on printed p. 115 reverses those lemma references: Lemma 11.4
is the primitive nonprincipal input. Semantic review: `SEM-528`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Metric Set
open scoped Interval

noncomputable section

/-- The selected-height conductor scale has logarithm at least one. -/
theorem one_le_dirichletHorizontalLogScale
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 2 ≤ T) :
    (1 : ℝ) ≤ Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscale : (4 : ℝ) ≤ (q : ℝ) * (T + 2) := by
    nlinarith [mul_le_mul hq (show (4 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ q)]
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9]
  exact hlogFour.le.trans (Real.log_le_log (by norm_num) hscale)

private theorem log_selectedHeightScale_le_two_mul
    {q : ℕ} [NeZero q] {T U : ℝ} (hT : 2 ≤ T)
    (hU : U ∈ Icc T (T + 1)) :
    Real.log ((q : ℝ) * (|U| + 2)) ≤
      2 * Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hargPos : 0 < (q : ℝ) * (|U| + 2) := by positivity
  have hheight : U + 2 ≤ (T + 2) ^ 2 := by
    nlinarith [hU.2, sq_nonneg T]
  have hlevel : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hscale : (q : ℝ) * (|U| + 2) ≤
      ((q : ℝ) * (T + 2)) ^ 2 := by
    rw [abs_of_nonneg hU0]
    calc
      (q : ℝ) * (U + 2) ≤ (q : ℝ) * (T + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hheight hq0
      _ ≤ (q : ℝ) ^ 2 * (T + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hlevel (sq_nonneg (T + 2))
      _ = ((q : ℝ) * (T + 2)) ^ 2 := by ring
  calc
    Real.log ((q : ℝ) * (|U| + 2)) ≤
        Real.log (((q : ℝ) * (T + 2)) ^ 2) :=
      Real.log_le_log hargPos hscale
    _ = 2 * Real.log ((q : ℝ) * (T + 2)) := by
      rw [Real.log_pow]
      norm_num

/-- At one already selected good height, the primitive nonprincipal
logarithmic derivative is uniformly bounded on both shallow horizontal
lines. -/
theorem exists_nat_norm_logDeriv_LFunction_primitive_horizontal_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ C : ℕ, 2 ≤ C →
        ∀ (q : ℕ) [NeZero q], 1 < q →
          ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
            ∀ (T U sigma : ℝ), 2 ≤ T →
              U ∈ Icc T (T + 1) →
                -1 ≤ sigma → sigma ≤ 3 →
                  (∀ rho : ℂ,
                    (rho ≠ 1 ∨ chi ≠ 1) →
                      DirichletCharacter.LFunction chi rho = 0 →
                        (1 / ((C : ℝ) *
                            Real.log ((q : ℝ) * (T + 2))) ≤
                          |U - rho.im|) ∧
                        (1 / ((C : ℝ) *
                            Real.log ((q : ℝ) * (T + 2))) ≤
                          |U + rho.im|)) →
                    ‖logDeriv (DirichletCharacter.LFunction chi)
                        ((sigma : ℂ) + U * I)‖ ≤
                      10 * (A : ℝ) * C *
                        Real.log ((q : ℝ) * (T + 2)) ^ 2 ∧
                    ‖logDeriv (DirichletCharacter.LFunction chi)
                        ((sigma : ℂ) - U * I)‖ ≤
                      10 * (A : ℝ) * C *
                        Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  obtain ⟨Af, hAf, hfixed⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le
  obtain ⟨Ad, _hAd, hmass⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  let A := max Af Ad
  refine ⟨A, hAf.trans (Nat.le_max_left Af Ad), ?_⟩
  intro C hC q _ hq chi hchi T U sigma hT hU hsigmaLower
    hsigmaUpper hclear
  let L : ℝ := Real.log ((q : ℝ) * (T + 2))
  let delta : ℝ := 1 / ((C : ℝ) * L)
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_dirichletHorizontalLogScale (q := q) hT
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hCLpos : 0 < (C : ℝ) * L :=
    mul_pos (by linarith) (by linarith)
  have hdelta : 0 < delta := by
    exact one_div_pos.mpr hCLpos
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hheightLog : Real.log ((q : ℝ) * (|U| + 2)) ≤ 2 * L := by
    simpa [L] using log_selectedHeightScale_le_two_mul (q := q) hT hU
  have hAfA : Af ≤ A := Nat.le_max_left Af Ad
  have hAdA : Ad ≤ A := Nat.le_max_right Af Ad
  have hAfAReal : (Af : ℝ) ≤ A := by exact_mod_cast hAfA
  have hAdAReal : (Ad : ℝ) ≤ A := by exact_mod_cast hAdA
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hbound : ∀ (t : ℝ), |t| = U →
      (∀ rho : ℂ, DirichletCharacter.LFunction chi rho = 0 →
        delta ≤ |t - rho.im|) →
      ∀ (r : ℝ), -1 ≤ r → r ≤ 3 →
        ‖logDeriv (DirichletCharacter.LFunction chi)
            ((r : ℂ) + t * I)‖ ≤
          10 * (A : ℝ) * C * L ^ 2 := by
    intro t htAbs hclearSigned r hrLower hrUpper
    let s : ℂ := (r : ℂ) + t * I
    let D : ℂ → ℤ :=
      MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6)
    have hlogt : Real.log ((q : ℝ) * (|t| + 2)) ≤ 2 * L := by
      simpa [htAbs, abs_of_nonneg hU0] using hheightLog
    have hlogt0 : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have hqOne : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      nlinarith [mul_le_mul hqOne
        (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ q)]
    have hsDisk : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
      rw [mem_closedBall, Complex.dist_eq]
      have hsSub : s - ((2 : ℂ) + t * I) = ((r - 2 : ℝ) : ℂ) := by
        dsimp [s]
        push_cast
        ring
      rw [hsSub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hsNonzero : DirichletCharacter.LFunction chi s ≠ 0 := by
      intro hsZero
      have hsep := hclearSigned s hsZero
      have hsim : s.im = t := by simp [s]
      rw [hsim, sub_self, abs_zero] at hsep
      linarith
    have hresidual0 := hfixed q hq chi hchi t s hsDisk hsNonzero
    have hprodResidual :
        (Af : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) ≤
          (A : ℝ) * (2 * L) :=
      mul_le_mul hAfAReal hlogt hlogt0 hA0
    have hresidual :
        ‖logDeriv (DirichletCharacter.LFunction chi) s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
          32 * (A : ℝ) * L / 3 := by
      calc
        ‖logDeriv (DirichletCharacter.LFunction chi) s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
            16 * ((Af : ℝ) *
              Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
          simpa [D] using hresidual0
        _ ≤ 16 * ((A : ℝ) * (2 * L)) / 3 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprodResidual (by norm_num)) (by norm_num)
        _ = 32 * (A : ℝ) * L / 3 := by ring
    have hDfinite : D.support.Finite := by
      simpa [D] using divisor_LFunction_closedBall_support_finite hchiNe
        ((2 : ℂ) + t * I) 6
    have hDnonneg : 0 ≤ D := by
      intro rho
      exact (divisor_LFunction_nonneg hchiNe
        (closedBall ((2 : ℂ) + t * I) 6)) rho
    have hDsep : ∀ rho ∈ D.support, delta ≤ ‖s - rho‖ := by
      intro rho hrho
      have hrhoDisk : rho ∈ closedBall ((2 : ℂ) + t * I) 6 := by
        exact (MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6)).supportWithinDomain
            (by simpa [D] using hrho)
      have hrhoZero : DirichletCharacter.LFunction chi rho = 0 :=
        (mem_support_divisor_LFunction_iff hchiNe hrhoDisk).1 (by
          simpa [D] using hrho)
      calc
        delta ≤ |t - rho.im| := hclearSigned rho hrhoZero
        _ = |(s - rho).im| := by simp [s]
        _ ≤ ‖s - rho‖ := Complex.abs_im_le_norm _
    have hsum0 := norm_finsum_intCast_div_sub_le D hDfinite hDnonneg
      hdelta hDsep
    have hmass0 := hmass q hq chi hchi t
    have hprodMass :
        (Ad : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) ≤
          (A : ℝ) * (2 * L) :=
      mul_le_mul hAdAReal hlogt hlogt0 hA0
    have hmassBound :
        ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) ≤ 4 * (A : ℝ) * L := by
      calc
        ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) ≤
            2 * (Ad : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) := by
          simpa [D] using hmass0
        _ ≤ 2 * ((A : ℝ) * (2 * L)) := by nlinarith
        _ = 4 * (A : ℝ) * L := by ring
    have hsum :
        ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
          4 * (A : ℝ) * C * L ^ 2 := by
      calc
        ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
            ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) / delta := hsum0
        _ ≤ (4 * (A : ℝ) * L) / delta :=
          div_le_div_of_nonneg_right hmassBound hdelta.le
        _ = 4 * (A : ℝ) * C * L ^ 2 := by
          dsimp [delta]
          field_simp
    have hCLtwo : (2 : ℝ) ≤ (C : ℝ) * L := by
      nlinarith [mul_le_mul hCreal hLone (by norm_num : (0 : ℝ) ≤ 1) hC0]
    have hAL0 : 0 ≤ (A : ℝ) * L := mul_nonneg hA0 hL0
    have hscaleProduct :
        2 * ((A : ℝ) * L) ≤ ((C : ℝ) * L) * ((A : ℝ) * L) :=
      mul_le_mul_of_nonneg_right hCLtwo hAL0
    calc
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ =
          ‖(logDeriv (DirichletCharacter.LFunction chi) s -
              ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)) +
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := by ring_nf
      _ ≤ ‖logDeriv (DirichletCharacter.LFunction chi) s -
              ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ +
            ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := norm_add_le _ _
      _ ≤ 32 * (A : ℝ) * L / 3 +
            4 * (A : ℝ) * C * L ^ 2 := add_le_add hresidual hsum
      _ ≤ 10 * (A : ℝ) * C * L ^ 2 := by
        nlinarith [hscaleProduct]
  constructor
  · exact hbound U (abs_of_nonneg hU0)
      (fun rho hrho => (hclear rho (Or.inr hchiNe) hrho).1)
      sigma hsigmaLower hsigmaUpper
  · have hlower := hbound (-U) (by rw [abs_neg, abs_of_nonneg hU0])
        (fun rho hrho => by
          have hc := (hclear rho (Or.inr hchiNe) hrho).2
          convert hc using 1
          rw [show -U - rho.im = -(U + rho.im) by ring, abs_neg])
        sigma hsigmaLower hsigmaUpper
    simpa [L, sub_eq_add_neg] using hlower


end

end BoundedGaps.Maynard
