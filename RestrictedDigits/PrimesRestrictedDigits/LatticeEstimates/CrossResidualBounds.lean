import PrimesRestrictedDigits.LatticeEstimates.CrossProduct

/-!
# Quantitative cross-product residual bounds

This file packages the elementary norm estimates following the exact
dual-basis identity in `CrossProduct.lean`.  The residual is transported from
coordinate functions to the Euclidean `L2` space before taking its norm.
-/

noncomputable section

namespace PrimesRestrictedDigits

open Matrix Real WithLp

open scoped Matrix

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The Euclidean-space version of `crossResidual`. -/
def euclideanCrossResidual (A u v : E) : E :=
  WithLp.toLp 2 (crossResidual A.ofLp u.ofLp v.ofLp)

@[simp] theorem euclideanCrossResidual_ofLp (A u v : E) :
    (euclideanCrossResidual A u v).ofLp =
      crossResidual A.ofLp u.ofLp v.ofLp := by
  rfl

/-- Generic residual estimate in terms of the two scalar products and basis
norms.  This is the analytic part of the repaired Lemma 14.1 argument. -/
theorem norm_euclideanCrossResidual_le
    (A u v : E) (hc : euclideanCross u v ≠ 0)
    {s0 s1 U0 U1 : Real}
    (hs0 : |inner Real A u| <= s0)
    (hs1 : |inner Real A v| <= s1)
    (hU0 : ‖u‖ <= U0) (hU1 : ‖v‖ <= U1) :
    ‖euclideanCrossResidual A u v‖ <=
      (s0 * U1 + s1 * U0) / ‖euclideanCross u v‖ := by
  let c : E := euclideanCross u v
  have hc0 : c ≠ 0 := by simpa [c] using hc
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hdot : (c.ofLp ⬝ᵥ c.ofLp) = inner Real c c := by
    rw [PiLp.inner_apply]
    simp [dotProduct, pow_two]
  have hAu : A.ofLp ⬝ᵥ u.ofLp = inner Real A u := by
    rw [PiLp.inner_apply]
    simp [dotProduct, mul_comm]
  have hAv : A.ofLp ⬝ᵥ v.ofLp = inner Real A v := by
    rw [PiLp.inner_apply]
    simp [dotProduct, mul_comm]
  have hcc : (u.ofLp ⨯₃ v.ofLp) ⬝ᵥ (u.ofLp ⨯₃ v.ofLp) =
      ‖c‖ ^ 2 := by
    calc
      (u.ofLp ⨯₃ v.ofLp) ⬝ᵥ (u.ofLp ⨯₃ v.ofLp) = c.ofLp ⬝ᵥ c.ofLp := by
        congr 1
      _ = inner Real c c := hdot
      _ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
  have hcross := crossResidual_eq_crossDualResidual
    A.ofLp u.ofLp v.ofLp (by
      intro h
      apply hc0
      have hz : WithLp.toLp 2 ((u.ofLp) ⨯₃ (v.ofLp)) = 0 := by
        simpa [c, euclideanCross] using h
      have hz' : c = 0 := by
        simpa [c, euclideanCross] using hz
      exact hz')
  have hres : euclideanCrossResidual A u v =
      (inner Real A u / (inner Real c c)) • euclideanCross v c +
        (inner Real A v / (inner Real c c)) • euclideanCross c u := by
    apply WithLp.ofLp_injective 2
    simp only [euclideanCrossResidual, WithLp.ofLp_toLp, WithLp.ofLp_add,
      WithLp.ofLp_smul]
    rw [hcross]
    simp [crossDualResidual, c, euclideanCross, PiLp.inner_apply, hAu, hAv, hcc]
  have hnorm_add :
      ‖euclideanCrossResidual A u v‖ <=
        ‖inner Real A u / (inner Real c c)‖ * ‖euclideanCross v c‖ +
          ‖inner Real A v / (inner Real c c)‖ * ‖euclideanCross c u‖ := by
    calc
      ‖euclideanCrossResidual A u v‖ <=
          ‖(inner Real A u / (inner Real c c)) • euclideanCross v c‖ +
            ‖(inner Real A v / (inner Real c c)) • euclideanCross c u‖ := by
        rw [hres]
        exact norm_add_le _ _
      _ = ‖inner Real A u / (inner Real c c)‖ * ‖euclideanCross v c‖ +
            ‖inner Real A v / (inner Real c c)‖ * ‖euclideanCross c u‖ := by
        rw [norm_smul, norm_smul]
  have hden : inner Real c c = ‖c‖ ^ 2 := by
    exact real_inner_self_eq_norm_sq c
  change ‖euclideanCrossResidual A u v‖ <=
    (s0 * U1 + s1 * U0) / ‖c‖
  have hnorm_add' := hnorm_add
  rw [hden] at hnorm_add'
  have hcross_vc : ‖euclideanCross v c‖ <= ‖v‖ * ‖c‖ :=
    norm_euclideanCross_le v c
  have hcross_cu : ‖euclideanCross c u‖ <= ‖c‖ * ‖u‖ :=
    norm_euclideanCross_le c u
  have hnormsq_nonneg : 0 <= ‖c‖ ^ 2 := sq_nonneg _
  have hdennorm : ‖(‖c‖ ^ 2 : Real)‖ = ‖c‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnormsq_nonneg]
  have hnorm_div0 :
      ‖inner Real A u / (‖c‖ ^ 2)‖ = ‖inner Real A u‖ / ‖c‖ ^ 2 := by
    rw [norm_div, hdennorm]
  have hnorm_div1 :
      ‖inner Real A v / (‖c‖ ^ 2)‖ = ‖inner Real A v‖ / ‖c‖ ^ 2 := by
    rw [norm_div, hdennorm]
  have hnorm_add'' :
      ‖euclideanCrossResidual A u v‖ <=
        ‖inner Real A u‖ / ‖c‖ ^ 2 * ‖euclideanCross v c‖ +
          ‖inner Real A v‖ / ‖c‖ ^ 2 * ‖euclideanCross c u‖ := by
    calc
      ‖euclideanCrossResidual A u v‖ <=
          ‖inner Real A u / (‖c‖ ^ 2)‖ * ‖euclideanCross v c‖ +
            ‖inner Real A v / (‖c‖ ^ 2)‖ * ‖euclideanCross c u‖ := hnorm_add'
      _ = ‖inner Real A u‖ / ‖c‖ ^ 2 * ‖euclideanCross v c‖ +
            ‖inner Real A v‖ / ‖c‖ ^ 2 * ‖euclideanCross c u‖ := by
        rw [hnorm_div0, hnorm_div1]
  have hbound :
      ‖inner Real A u‖ / ‖c‖ ^ 2 * ‖euclideanCross v c‖ +
          ‖inner Real A v‖ / ‖c‖ ^ 2 * ‖euclideanCross c u‖ <=
        (s0 * U1 + s1 * U0) / ‖c‖ := by
    have hs0' : 0 <= s0 := le_trans (abs_nonneg _) hs0
    have hs1' : 0 <= s1 := le_trans (abs_nonneg _) hs1
    have hinner0 : ‖inner Real A u‖ <= s0 := by
      simpa [Real.norm_eq_abs] using hs0
    have hinner1 : ‖inner Real A v‖ <= s1 := by
      simpa [Real.norm_eq_abs] using hs1
    have hD : 0 < ‖c‖ ^ 2 := sq_pos_of_pos hcnorm
    have hterm0 : ‖inner Real A u‖ / ‖c‖ ^ 2 * ‖euclideanCross v c‖ <=
        s0 * (‖v‖ * ‖c‖) / ‖c‖ ^ 2 := by
      have hprod : ‖inner Real A u‖ * ‖euclideanCross v c‖ <=
          s0 * (‖v‖ * ‖c‖) :=
        mul_le_mul hinner0 hcross_vc (norm_nonneg _) hs0'
      calc
        ‖inner Real A u‖ / ‖c‖ ^ 2 * ‖euclideanCross v c‖ =
            (‖inner Real A u‖ * ‖euclideanCross v c‖) / ‖c‖ ^ 2 := by ring
        _ <= (s0 * (‖v‖ * ‖c‖)) / ‖c‖ ^ 2 :=
          div_le_div_of_nonneg_right hprod hD.le
    have hterm1 : ‖inner Real A v‖ / ‖c‖ ^ 2 * ‖euclideanCross c u‖ <=
        s1 * (‖c‖ * ‖u‖) / ‖c‖ ^ 2 := by
      have hprod : ‖inner Real A v‖ * ‖euclideanCross c u‖ <=
          s1 * (‖c‖ * ‖u‖) :=
        mul_le_mul hinner1 hcross_cu (norm_nonneg _) hs1'
      calc
        ‖inner Real A v‖ / ‖c‖ ^ 2 * ‖euclideanCross c u‖ =
            (‖inner Real A v‖ * ‖euclideanCross c u‖) / ‖c‖ ^ 2 := by ring
        _ <= (s1 * (‖c‖ * ‖u‖)) / ‖c‖ ^ 2 :=
          div_le_div_of_nonneg_right hprod hD.le
    have hsum := add_le_add hterm0 hterm1
    have hcancel :
        s0 * (‖v‖ * ‖c‖) / ‖c‖ ^ 2 +
            s1 * (‖c‖ * ‖u‖) / ‖c‖ ^ 2 =
          (s0 * ‖v‖ + s1 * ‖u‖) / ‖c‖ := by
      field_simp [ne_of_gt hcnorm]
    rw [hcancel] at hsum
    have hnum : s0 * ‖v‖ + s1 * ‖u‖ <= s0 * U1 + s1 * U0 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hU1 hs0')
        (mul_le_mul_of_nonneg_left hU0 hs1')
    have hlast :
        (s0 * ‖v‖ + s1 * ‖u‖) / ‖c‖ <=
          (s0 * U1 + s1 * U0) / ‖c‖ :=
      div_le_div_of_nonneg_right hnum hcnorm.le
    exact le_trans hsum hlast
  exact le_trans hnorm_add'' hbound

/-- A cross product of two integral triples has the explicit upper bound used
in the repaired lattice argument. -/
theorem norm_euclideanCross_intVectors_le
    (z0 z1 : Fin 3 -> Int) (V0 V1 delta K : Real)
    (hV0 : 0 <= V0) (_hV1 : 0 <= V1)
    (hw0 : ‖intVectorToEuclidean z0‖ <= 28 * V0)
    (hw1 : ‖intVectorToEuclidean z1‖ <= 28 * V1)
    (_hdelta : 0 < delta) (_hK : 0 < K)
    (hproduct : V0 * V1 <= 900 / (delta * K)) :
    ‖euclideanCross (intVectorToEuclidean z0) (intVectorToEuclidean z1)‖ <=
      705600 / (delta * K) := by
  let w0 : E := intVectorToEuclidean z0
  let w1 : E := intVectorToEuclidean z1
  have hmul : ‖w0‖ * ‖w1‖ <= (28 * V0) * (28 * V1) := by
    exact mul_le_mul hw0 hw1 (norm_nonneg _) (by positivity)
  calc
    ‖euclideanCross w0 w1‖ <= ‖w0‖ * ‖w1‖ := norm_euclideanCross_le w0 w1
    _ <= (28 * V0) * (28 * V1) := hmul
    _ = 784 * (V0 * V1) := by ring
    _ <= 784 * (900 / (delta * K)) :=
      mul_le_mul_of_nonneg_left hproduct (by norm_num)
    _ = 705600 / (delta * K) := by ring

/-- The same cross-product upper bound written with the literal integer
cross-product and its Euclidean cast. -/
theorem norm_intVectorCross_le
    (z0 z1 : Fin 3 -> Int) (V0 V1 delta K : Real)
    (hV0 : 0 <= V0) (_hV1 : 0 <= V1)
    (hw0 : ‖intVectorToEuclidean z0‖ <= 28 * V0)
    (hw1 : ‖intVectorToEuclidean z1‖ <= 28 * V1)
    (_hdelta : 0 < delta) (_hK : 0 < K)
    (hproduct : V0 * V1 <= 900 / (delta * K)) :
    ‖intVectorToEuclidean (z0 ⨯₃ z1)‖ <= 705600 / (delta * K) := by
  simpa [intVectorToEuclidean_cross] using
    (norm_euclideanCross_intVectors_le z0 z1 V0 V1 delta K hV0 _hV1
      hw0 hw1 _hdelta _hK hproduct)

/-- Integrality gives a unit lower bound for a nonzero integral cross product. -/
theorem one_le_norm_euclideanCross_intVectors
    (z0 z1 : Fin 3 -> Int)
    (hLI : LinearIndependent Real
      ![intVectorToEuclidean z0, intVectorToEuclidean z1]) :
    1 <= ‖euclideanCross (intVectorToEuclidean z0) (intVectorToEuclidean z1)‖ := by
  have hc : euclideanCross (intVectorToEuclidean z0) (intVectorToEuclidean z1) ≠ 0 :=
    (euclideanCross_ne_zero_iff).2 hLI
  have hz : z0 ⨯₃ z1 ≠ 0 := by
    intro hz
    apply hc
    rw [← intVectorToEuclidean_cross]
    simp [hz]
  simpa [intVectorToEuclidean_cross] using
    (one_le_norm_intVectorToEuclidean hz)

/-- The unit lower bound in literal integer-cross notation. -/
theorem one_le_norm_intVectorCross
    (z0 z1 : Fin 3 -> Int)
    (hLI : LinearIndependent Real
      ![intVectorToEuclidean z0, intVectorToEuclidean z1]) :
    1 <= ‖intVectorToEuclidean (z0 ⨯₃ z1)‖ := by
  simpa [intVectorToEuclidean_cross] using
    (one_le_norm_euclideanCross_intVectors z0 z1 hLI)

/-- Linear independence of integral representatives makes their Euclidean
cross product nonzero. -/
theorem euclideanCross_intVectors_ne_zero_of_linearIndependent
    (z0 z1 : Fin 3 -> Int)
    (hLI : LinearIndependent Real
      ![intVectorToEuclidean z0, intVectorToEuclidean z1]) :
    euclideanCross (intVectorToEuclidean z0) (intVectorToEuclidean z1) ≠ 0 :=
  (euclideanCross_ne_zero_iff).2 hLI

/-- The residual estimate after inserting the inverse-dilation and reduced
basis constants. -/
theorem norm_euclideanCrossResidual_le_of_basis_bounds
    (A u v : E) (X delta N K V0 V1 : Real)
    (hX : 0 <= X) (hdelta : 0 < delta) (hN : 0 < N) (hK : 0 < K)
    (hLI : LinearIndependent Real ![u, v])
    (_hV0 : 0 <= V0) (_hV1 : 0 <= V1)
    (hw0 : ‖u‖ <= 28 * V0) (hw1 : ‖v‖ <= 28 * V1)
    (hi0 : |inner Real A u| <= 3 * delta * X * V0 / N)
    (hi1 : |inner Real A v| <= 3 * delta * X * V1 / N)
    (hproduct : V0 * V1 <= 900 / (delta * K)) :
    ‖euclideanCrossResidual A u v‖ <=
      151200 * X / (N * K * ‖euclideanCross u v‖) := by
  have hc : euclideanCross u v ≠ 0 := (euclideanCross_ne_zero_iff).2 hLI
  have hgeneric := norm_euclideanCrossResidual_le A u v hc
    (s0 := 3 * delta * X * V0 / N)
    (s1 := 3 * delta * X * V1 / N)
    (U0 := 28 * V0) (U1 := 28 * V1)
    hi0 hi1 hw0 hw1
  have hcoef : 0 <= 168 * delta * X / N := by positivity
  have hscaled :
      (168 * delta * X / N) * (V0 * V1) <=
        (168 * delta * X / N) * (900 / (delta * K)) :=
    mul_le_mul_of_nonneg_left hproduct hcoef
  have hnum :
      (3 * delta * X * V0 / N) * (28 * V1) +
          (3 * delta * X * V1 / N) * (28 * V0) <=
        151200 * X / (N * K) := by
    calc
      (3 * delta * X * V0 / N) * (28 * V1) +
          (3 * delta * X * V1 / N) * (28 * V0) =
        (168 * delta * X / N) * (V0 * V1) := by ring
      _ <= (168 * delta * X / N) * (900 / (delta * K)) := hscaled
      _ = 151200 * X / (N * K) := by
        field_simp [hdelta.ne', hN.ne', hK.ne']
        ring
  calc
    ‖euclideanCrossResidual A u v‖ <=
        ((3 * delta * X * V0 / N) * (28 * V1) +
          (3 * delta * X * V1 / N) * (28 * V0)) /
            ‖euclideanCross u v‖ := hgeneric
    _ <= (151200 * X / (N * K)) / ‖euclideanCross u v‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = 151200 * X / (N * K * ‖euclideanCross u v‖) := by ring

/-- Integer-coordinate wrapper for `norm_euclideanCrossResidual_le_of_basis_bounds`. -/
theorem norm_euclideanCrossResidual_intVectors_le
    (A : E) (z0 z1 : Fin 3 -> Int) (X delta N K V0 V1 : Real)
    (hX : 0 <= X) (hdelta : 0 < delta) (hN : 0 < N) (hK : 0 < K)
    (hLI : LinearIndependent Real
      ![intVectorToEuclidean z0, intVectorToEuclidean z1])
    (hV0 : 0 <= V0) (hV1 : 0 <= V1)
    (hw0 : ‖intVectorToEuclidean z0‖ <= 28 * V0)
    (hw1 : ‖intVectorToEuclidean z1‖ <= 28 * V1)
    (hi0 : |inner Real A (intVectorToEuclidean z0)| <=
      3 * delta * X * V0 / N)
    (hi1 : |inner Real A (intVectorToEuclidean z1)| <=
      3 * delta * X * V1 / N)
    (hproduct : V0 * V1 <= 900 / (delta * K)) :
    ‖euclideanCrossResidual A (intVectorToEuclidean z0)
      (intVectorToEuclidean z1)‖ <=
      151200 * X /
        (N * K * ‖euclideanCross (intVectorToEuclidean z0)
          (intVectorToEuclidean z1)‖) := by
  exact norm_euclideanCrossResidual_le_of_basis_bounds
    A (intVectorToEuclidean z0) (intVectorToEuclidean z1)
    X delta N K V0 V1 hX hdelta hN hK hLI hV0 hV1 hw0 hw1 hi0 hi1 hproduct

end PrimesRestrictedDigits
