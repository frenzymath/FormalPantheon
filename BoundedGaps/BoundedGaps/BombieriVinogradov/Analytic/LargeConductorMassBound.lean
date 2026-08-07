import BoundedGaps.BombieriVinogradov.Analytic.AllModulusConductorSplit
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanConductorConclusion

/-!
# Large-conductor all-modulus mass bound

This file estimates the large-inducing-conductor branch of SEM-463. It
regroups the exact positive factor-pair sum, applies the reciprocal-totient
prefix estimate, replaces centered primitive maxima by raw maxima above level
one, and then invokes the audited Vaughan primitive-mean Abel estimate.

Sources: `Vaughan1980`, p. 113, and `AkbaryHambrook2013v2`, Section 7,
pp. 24--25. Semantic review: `SEM-464`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- Regroup the large-conductor factor-pair mass by conductor and its positive
multiplier. The assumption `1 <= R` makes the separate conductor-one exclusion
redundant on the interval `R < d`. -/
theorem largeConductorCenteredMass_eq_sum_multipliers
    (x Q R : ℕ) (hR : 1 ≤ R) :
    largeConductorCenteredMass x Q R =
      ∑ d ∈ Finset.Ioc R Q,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ := by
  classical
  unfold largeConductorCenteredMass
  let S : Finset (ℕ × ℕ) :=
    (positiveFactorPairs Q).filter (fun p ↦ p.1 ≠ 1 ∧ R < p.1)
  let T : Finset ((d : ℕ) × ℕ) :=
    Finset.sigma (Finset.Ioc R Q) (fun d ↦ Finset.Ioc 0 (Q / d))
  let F : ℕ × ℕ → ℝ := fun p ↦
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ
  have hbij : (∑ p ∈ S, F p) = ∑ z ∈ T, F (z.1, z.2) := by
    apply Finset.sum_bij (fun p _hp ↦ ⟨p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpairs, _hdne, hRd⟩
      rcases Finset.mem_filter.mp hpairs with ⟨hprodmem, hprod⟩
      rcases Finset.mem_product.mp hprodmem with ⟨hdmem, hkmem⟩
      have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hdmem).1
      have hkdiv : p.2 ≤ Q / p.1 := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        simpa [Nat.mul_comm] using hprod
      exact Finset.mem_sigma.mpr ⟨
        Finset.mem_Ioc.mpr ⟨hRd, (Finset.mem_Ioc.mp hdmem).2⟩,
        Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkmem).1, hkdiv⟩⟩
    · intro p _hp p' _hp' heq
      apply Prod.ext
      · exact congrArg Sigma.fst heq
      · exact congrArg Sigma.snd heq
    · intro z hz
      rcases z with ⟨d, k⟩
      rcases Finset.mem_sigma.mp hz with ⟨hdmem, hkmem⟩
      have hdBounds := Finset.mem_Ioc.mp hdmem
      have hdpos : 0 < d := (Nat.zero_lt_one.trans_le hR).trans hdBounds.1
      have hkBounds := Finset.mem_Ioc.mp hkmem
      have hprod : d * k ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hdpos).1 hkBounds.2
        simpa [Nat.mul_comm] using h
      have hkQ : k ≤ Q := hkBounds.2.trans (Nat.div_le_self Q d)
      have hpairs : (d, k) ∈ positiveFactorPairs Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨
          Finset.mem_Ioc.mpr ⟨hdpos, hdBounds.2⟩,
          Finset.mem_Ioc.mpr ⟨hkBounds.1, hkQ⟩⟩, hprod⟩
      refine ⟨(d, k), Finset.mem_filter.mpr ⟨hpairs, ?_, hdBounds.1⟩, ?_⟩
      · exact (hR.trans_lt hdBounds.1).ne'
      · rfl
    · intro p _hp
      rfl
  have hsum := Finset.sum_sigma' (Finset.Ioc R Q)
    (fun d ↦ Finset.Ioc 0 (Q / d)) (fun d k ↦ F (d, k))
  calc
    (∑ p ∈ S, F p) =
        ∑ d ∈ Finset.Ioc R Q,
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ *
              ∑ ψ : primitiveCharacters d,
                primitiveCenteredEndpointMaximum x d ψ := by
      simpa [T, F] using hbij.trans hsum.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [mul_comm]

/-- The large-conductor mass is bounded by the normalized raw primitive mean
over the exact natural conductor interval. -/
theorem largeConductorCenteredMass_le_five_log_meanValueInterval
    (x Q R : ℕ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) (hR : 1 ≤ R) :
    largeConductorCenteredMass x Q R ≤
      (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc R Q,
          primitiveRawMeanValueWeight x d / (d : ℝ) := by
  rw [largeConductorCenteredMass_eq_sum_multipliers x Q R hR]
  calc
    (∑ d ∈ Finset.Ioc R Q,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹) ≤
        ∑ d ∈ Finset.Ioc R Q,
          (∑ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ) *
            ((d.totient : ℝ)⁻¹ *
              ∑ k ∈ Finset.Ioc 0 (Q / d),
                (k.totient : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro d hdmem
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_totient_mul_le_inv_totient_mul_sum Q d
          ((Nat.zero_lt_one.trans_le hR).trans (Finset.mem_Ioc.mp hdmem).1)
      · exact sum_primitiveCenteredEndpointMaximum_nonneg x d
    _ ≤ ∑ d ∈ Finset.Ioc R Q,
          (∑ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ) *
            ((d.totient : ℝ)⁻¹ * (5 * Real.log (x : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdBounds := Finset.mem_Ioc.mp hdmem
      have hdpos : 0 < d := (Nat.zero_lt_one.trans_le hR).trans hdBounds.1
      have hK : 0 < Q / d := Nat.div_pos hdBounds.2 hdpos
      have hprefix :
          (∑ k ∈ Finset.Ioc 0 (Q / d), (k.totient : ℝ)⁻¹) ≤
            4 * (1 + Real.log ((Q / d : ℕ) : ℝ)) := by
        simpa [reciprocalTotientPrefix] using
          (reciprocalTotientPrefix_le_four_mul_one_add_log hK)
      have hlog := four_mul_one_add_log_natDiv_lt_five_mul_log
        hx hdpos hdBounds.2 hQsqrt
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left (hprefix.trans hlog.le)
        positivity
      · exact sum_primitiveCenteredEndpointMaximum_nonneg x d
    _ = (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc R Q,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc R Q,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveRawEndpointMaximum x d ψ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [sum_primitiveCenteredEndpointMaximum_eq_raw x
        (hR.trans_lt (Finset.mem_Ioc.mp hdmem).1)]
    _ = (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc R Q,
          primitiveRawMeanValueWeight x d / (d : ℝ) := by
      congr 1
      simpa only [Nat.floor_natCast] using
        (sum_interval_invTotient_primitiveRaw_eq_meanValueWeight_div
          x Q (R : ℝ))

/-- Generic large-conductor conclusion after inserting a global Chebyshev
upper bound into the Vaughan primitive-mean Abel estimate. -/
theorem largeConductorCenteredMass_le_abelEnvelope_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x Q R : ℕ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hR : 1 ≤ R) (hRQ : R ≤ Q) :
    largeConductorCenteredMass x Q R ≤
      (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
        vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRQreal : (R : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hRQ
  have habelEq :
      (∑ d ∈ Finset.Ioc R Q,
          primitiveRawMeanValueWeight x d / (d : ℝ)) =
        (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
          (R : ℝ)⁻¹ * primitiveRawMeanValueCumulative x R +
            ∫ t in Set.Ioc (R : ℝ) (Q : ℝ),
              primitiveRawMeanValueCumulative x t / t ^ 2 := by
    simpa only [Nat.floor_natCast] using
      (sum_meanValueWeight_div_eq_rawPrimitiveAbel_natUpper
        x Q (R : ℝ) hRreal hRQreal)
  have habelBound :=
    primitiveRawMeanValueAbelExpression_natUpper_le_envelope_of_psi
      hA hpsi hx hRreal hRQreal hQsqrt
  have hlog : 0 ≤ 5 * Real.log (x : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  calc
    largeConductorCenteredMass x Q R ≤
        (5 * Real.log (x : ℝ)) *
          ∑ d ∈ Finset.Ioc R Q,
            primitiveRawMeanValueWeight x d / (d : ℝ) :=
      largeConductorCenteredMass_le_five_log_meanValueInterval
        x Q R hx hQsqrt hR
    _ = (5 * Real.log (x : ℝ)) *
        ((Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
          (R : ℝ)⁻¹ * primitiveRawMeanValueCumulative x R +
            ∫ t in Set.Ioc (R : ℝ) (Q : ℝ),
              primitiveRawMeanValueCumulative x t / t ^ 2) := by rw [habelEq]
    _ ≤ (5 * Real.log (x : ℝ)) *
        (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
            vaughanPrimitiveMeanEquationOneOneLogPower x) :=
      mul_le_mul_of_nonneg_left habelBound hlog
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
          ((5 * Real.log (x : ℝ)) *
            vaughanPrimitiveMeanEquationOneOneLogPower x) := by ring
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
          (5 * vaughanPrimitiveMeanEquationOneTwoLogPower x) := by
      rw [five_log_mul_equationOneOneLogPower]
    _ = (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
        vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring

/-- Unconditional large-conductor estimate using Mathlib's verified global
Chebyshev constant. -/
theorem largeConductorCenteredMass_le_abelEnvelope
    (x Q R : ℕ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hR : 1 ≤ R) (hRQ : R ≤ Q) :
    largeConductorCenteredMass x Q R ≤
      (5 * vaughanPrimitiveMeanEquationOneOneConstant
          (Real.log 4 + 4)) *
        vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  refine largeConductorCenteredMass_le_abelEnvelope_of_psi
    (A := Real.log 4 + 4) ?_ ?_ x Q R hx hQsqrt hR hRQ
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz

end

end BoundedGaps.Maynard
