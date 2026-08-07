import BoundedGaps.BombieriVinogradov.Analytic.RawPrimitiveAbelSummation
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFiveTermEndpoint
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermEquation
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermLargeEquation

/-!
# Vaughan primitive mean assembly

This file combines the five endpoint maxima in Vaughan's decomposition with
their existing numerical estimates. It stops before the piecewise choice of
the cutoff parameters `U` and `V` in Akbary--Hambrook's proof of Theorem 1.2.

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 18--24. Semantic
review: `SEM-459`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- At a natural cutoff, the cumulative raw mean is exactly the source's
positive-level weighted primitive-character sum. -/
theorem primitiveRawMeanValueCumulative_nat_eq_weightedRawEndpointMaximum
    (x Q : ℕ) :
    primitiveRawMeanValueCumulative x Q =
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            primitiveRawEndpointMaximum x q chi := by
  rw [primitiveRawMeanValueCumulative_nat]
  change (∑ q ∈ Finset.Icc 0 Q, primitiveRawMeanValueWeight x q) =
    ∑ q ∈ Finset.Ioc 0 Q, primitiveRawMeanValueWeight x q
  symm
  apply Finset.sum_subset
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le q, (Finset.mem_Ioc.mp hq).2⟩
  · intro q hqIcc hqNotIoc
    have hqZero : q = 0 := by
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hqNonneg, hqQ⟩
      by_contra hqNe
      exact hqNotIoc (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hqNe, hqQ⟩)
    subst q
    exact primitiveRawMeanValueWeight_zero x

/-- The all-cutoff Chebyshev bound, including the separate source boundary
cases `Q = 0` and `Q = 1`. -/
theorem primitiveRawMeanValueCumulative_nat_le_psi_mul_sq
    (x Q : ℕ) :
    primitiveRawMeanValueCumulative x Q ≤
      Chebyshev.psi x * (Q : ℝ) ^ 2 := by
  rw [primitiveRawMeanValueCumulative_nat_eq_weightedRawEndpointMaximum]
  have hpsi : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            primitiveRawEndpointMaximum x q chi) ≤
        ∑ q ∈ Finset.Ioc 0 Q, (q : ℝ) * Chebyshev.psi x := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
      have hphi : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hmass :
          (∑ chi : primitiveCharacters q,
              primitiveRawEndpointMaximum x q chi) ≤
            (q.totient : ℝ) * Chebyshev.psi x := by
        calc
          (∑ chi : primitiveCharacters q,
              primitiveRawEndpointMaximum x q chi) ≤
              ∑ _chi : primitiveCharacters q, Chebyshev.psi x := by
            apply Finset.sum_le_sum
            intro chi _hchi
            exact primitiveRawEndpointMaximum_le_psi x q chi
          _ = (Fintype.card (primitiveCharacters q) : ℝ) *
              Chebyshev.psi x := by simp
          _ ≤ (q.totient : ℝ) * Chebyshev.psi x := by
            apply mul_le_mul_of_nonneg_right _ hpsi
            exact_mod_cast card_primitiveCharacters_le_totient hqpos
      calc
        (q : ℝ) / (q.totient : ℝ) *
            (∑ chi : primitiveCharacters q,
              primitiveRawEndpointMaximum x q chi) ≤
            (q : ℝ) / (q.totient : ℝ) *
              ((q.totient : ℝ) * Chebyshev.psi x) := by
          exact mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = (q : ℝ) * Chebyshev.psi x := by field_simp
    _ ≤ ∑ _q ∈ Finset.Ioc 0 Q,
        (Q : ℝ) * Chebyshev.psi x := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right _ hpsi
      exact_mod_cast (Finset.mem_Ioc.mp hq).2
    _ = Chebyshev.psi x * (Q : ℝ) ^ 2 := by
      simp [Nat.card_Ioc]
      ring

/-- Distribute the weighted character sum over the five nonnegative endpoint
maxima without changing any support or weight. -/
theorem sum_weightedPrimitiveVaughanFiveTermEndpointMajorant_eq
    (U V : ℝ) (x Q : ℕ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanFiveTermEndpointMajorant U V x q chi.1) =
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumOneEndpointMaximum U x q chi.1) +
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumTwoEndpointMaximum V x q chi.1) +
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumThreeSmallEndpointMaximum U V x q chi.1) +
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) +
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumFourEndpointMaximum U V x q chi.1) := by
  simp_rw [vaughanFiveTermEndpointMajorant, Finset.sum_add_distrib, mul_add]
  repeat rw [Finset.sum_add_distrib]

/-- The natural cumulative raw mean is bounded by the corresponding weighted
sum of the five endpoint majorants. -/
theorem primitiveRawMeanValueCumulative_nat_le_vaughanFiveTermAggregate
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {x Q : ℕ} (hx : 2 ≤ x) :
    primitiveRawMeanValueCumulative x Q ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanFiveTermEndpointMajorant U V x q chi.1 := by
  rw [primitiveRawMeanValueCumulative_nat_eq_weightedRawEndpointMaximum]
  apply Finset.sum_le_sum
  intro q _hq
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro chi _hchi
    exact primitiveRawEndpointMaximum_le_vaughanFiveTermEndpointMajorant
      hU hV hx chi
  · positivity

/-- The unsimplified sum of equations (6.7), (6.10), (6.12), (6.13), and
(6.15), with a generic proved Chebyshev constant and SEM-458's totalized
fourth-term scale logarithm. -/
noncomputable def vaughanPrimitiveMeanMajorant
    (A U V : ℝ) (x Q : ℕ) : ℝ :=
  A * U * (Q : ℝ) ^ 2 +
    ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V) *
      (Real.log ((x : ℝ) * V)) ^ 2 +
    ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U) *
      (Real.log ((x : ℝ) * U)) ^ 2 +
    akbaryHambrookC3 / Real.log 2 *
      ((x : ℝ) + (Q : ℝ) * Real.sqrt ((x : ℝ) * U * V) +
        Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
        (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
      (Real.log (2 * U * V)) ^ 2 * Real.log (4 * (x : ℝ)) +
    vaughanFourthBlockConstant A / Real.log 2 *
      ((x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
        Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
        (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
      (vaughanFourthScaleLog V x * Real.sqrt (vaughanFourthScaleLog V x)) *
      Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ))

/-- Pre-optimization primitive mean bound with an explicit global Chebyshev
majorant. -/
theorem primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant_of_psi
    {A U V : ℝ}
    (hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x Q : ℕ} (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hQ : 2 ≤ Q) (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x Q ≤
      vaughanPrimitiveMeanMajorant A U V x Q := by
  have hpsiU : Chebyshev.psi U ≤ A * U :=
    hpsi U (zero_le_one.trans hU)
  have hOne :=
    sum_weightedPrimitiveVaughanTwistedSumOneEndpointMaximum_le
      hpsiU x Q
  have hTwo :=
    (sum_weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_lt
      (V := V) (x := x) (Q := Q) hx hV hQ hQsqrt).le
  have hThreeSmall :=
    (sum_weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_lt
      (U := U) (V := V) (x := x) (Q := Q) hx hU hQ hQsqrt).le
  have hThreeLarge :=
    sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le
      (U := U) (V := V) (x := x) (Q := Q) (by omega) hU hV
  have hFour :=
    sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_of_psi
      (A := A) (U := U) (V := V) (x := x) (Q := Q)
      hA hpsi (by omega) hU hV
  calc
    primitiveRawMeanValueCumulative x Q ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanFiveTermEndpointMajorant U V x q chi.1 :=
      primitiveRawMeanValueCumulative_nat_le_vaughanFiveTermAggregate
        hU hV (by omega)
    _ =
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumOneEndpointMaximum U x q chi.1) +
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumTwoEndpointMaximum V x q chi.1) +
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumThreeSmallEndpointMaximum U V x q chi.1) +
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) +
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumFourEndpointMaximum U V x q chi.1) :=
      sum_weightedPrimitiveVaughanFiveTermEndpointMajorant_eq U V x Q
    _ ≤ vaughanPrimitiveMeanMajorant A U V x Q := by
      unfold vaughanPrimitiveMeanMajorant
      linarith

/-- Unconditional pre-optimization primitive mean bound using Mathlib's
verified Chebyshev constant. -/
theorem primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant
    {U V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hQ : 2 ≤ Q) (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x Q ≤
      vaughanPrimitiveMeanMajorant (Real.log 4 + 4) U V x Q := by
  apply
    primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant_of_psi
      (A := Real.log 4 + 4) (U := U) (V := V)
      (x := x) (Q := Q) (by positivity)
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz
  · exact hx
  · exact hU
  · exact hV
  · exact hQ
  · exact hQsqrt

/-- Real-floor wrapper for the generic pre-optimization primitive mean bound. -/
theorem primitiveRawMeanValueCumulative_le_vaughanPrimitiveMeanMajorant_of_psi
    {A U V t : ℝ}
    (hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x : ℕ} (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (ht : 2 ≤ ⌊t⌋₊)
    (htsqrt : (⌊t⌋₊ : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x t ≤
      vaughanPrimitiveMeanMajorant A U V x ⌊t⌋₊ := by
  simpa only [primitiveRawMeanValueCumulative, Nat.floor_natCast] using
    (primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant_of_psi
      (A := A) (U := U) (V := V) (x := x) (Q := ⌊t⌋₊)
      hA hpsi hx hU hV ht htsqrt)

/-- Real-floor wrapper for the unconditional pre-optimization primitive mean
bound. -/
theorem primitiveRawMeanValueCumulative_le_vaughanPrimitiveMeanMajorant
    {U V t : ℝ} {x : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (ht : 2 ≤ ⌊t⌋₊)
    (htsqrt : (⌊t⌋₊ : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x t ≤
      vaughanPrimitiveMeanMajorant (Real.log 4 + 4) U V x ⌊t⌋₊ := by
  simpa only [primitiveRawMeanValueCumulative, Nat.floor_natCast] using
    (primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant
      (U := U) (V := V) (x := x) (Q := ⌊t⌋₊)
      hx hU hV ht htsqrt)

end

end BoundedGaps.Maynard
