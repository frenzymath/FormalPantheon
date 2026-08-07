import BoundedGaps.Maynard.ConcreteS2OffFaceGoodMomentTerm
import BoundedGaps.Maynard.ConcreteS2GoodComplementOuterMomentLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory
open scoped BigOperators

set_option maxRecDepth 8000 in
theorem engelsmaS2OffFaceFaceIntegral_sq_eq_quadraticSum
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    {u : engelsmaOffFaceFinset m → ℕ}
    (hu : u ∈ engelsmaS2OffFaceGoodSupport
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m)
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    engelsmaS2CoordinateFiberFaceIntegral
        (engelsmaMaynardRadius alpha N) m
          (engelsmaOffFaceExtension m u) ^ 2 =
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFaceInnerCoefficient i cp *
              smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
              engelsmaS2OffFaceQuadraticIntegrand m
                (smallKFaceInnerExponent i cp +
                  smallKFaceInnerExponent j dp) (cp + dp)
                (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) := by
  have huData := mem_engelsmaS2OffFaceGoodSupport_iff.mp hu
  have hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (primorial (tripleLogCutoff (N - 1)))
      (engelsmaOffFaceExtension m u) := by
    apply isMaynardDivisorTuple_of_mem_support
    apply (engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
      (engelsmaMaynardRadius alpha N) (primorial (tripleLogCutoff (N - 1))) m u).2
    exact huData.1
  have hpoint := engelsmaS2CoordinateFiberFaceIntegral_sq_eq_faceQuadraticSum
    m hr hR (engelsmaOffFaceExtension_at m u)
  simpa [engelsmaS2OffFaceQuadraticIntegrand_normalized_eq] using hpoint

set_option maxRecDepth 9000 in
set_option maxHeartbeats 1400000 in
theorem eventually_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment_eq_monomialSum
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m =
        ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m
                  (smallKFaceInnerExponent i cp +
                    smallKFaceInnerExponent j dp) (cp + dp) := by
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR] with N hRN
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let H := engelsmaOffFaceFinset m
  let W := engelsmaMaynardModulus N
  let S := preSieveSingularSeries D
  let L := Real.log R
  let k := Fintype.card H
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hRN)
  have hpoint : ∀ u ∈ engelsmaS2OffFaceGoodSupport R D m,
      engelsmaS2CoordinateFiberFaceIntegral R m
          (engelsmaOffFaceExtension m u) ^ 2 =
        ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                engelsmaS2OffFaceQuadraticIntegrand m
                  (smallKFaceInnerExponent i cp +
                    smallKFaceInnerExponent j dp)
                  (cp + dp)
                  (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) := by
    intro u hu
    exact engelsmaS2OffFaceFaceIntegral_sq_eq_quadraticSum
      (alpha := alpha) (N := N) m hu hRN
  have hk : ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card =
      Fintype.card H := by
    have hfull : ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card =
        104 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ m)]
      simpa using BoundedGaps.engelsmaTuple_card
    have hoff : Fintype.card H = 104 := by
      simp [H, engelsmaOffFaceFinset,
        Finset.card_erase_of_mem m.property,
        BoundedGaps.engelsmaTuple_card]
    omega
  have hW : W = primorial D := by
    simp [W, D, engelsmaMaynardModulus]
  let G := engelsmaS2OffFaceGoodSupport R D m
  let Q : ℝ := (S * L) ^ k
  let weight : (H → ℕ) → ℝ := fun u => outerTupleWeight H W u
  let coeff : Fin 42 → Fin 42 → ℕ → ℕ → ℝ := fun i j cp dp =>
    ((smallKCoefficient i * smallKCoefficient j *
      smallKFaceInnerCoefficient i cp *
      smallKFaceInnerCoefficient j dp : ℚ) : ℝ)
  let f : Fin 42 → Fin 42 → ℕ → ℕ → (H → ℕ) → ℝ :=
    fun i j cp dp u => engelsmaS2OffFaceQuadraticIntegrand m
      (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
      (cp + dp) (engelsmaS2OffFaceNormalizedLogPoint alpha N m u)
  unfold normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
  rw [engelsmaS2CoordinateFiberGoodComplementOuterMoment_eq_offFace m hRN]
  unfold engelsmaS2OffFaceGoodComplementOuterMoment
    normalizedEngelsmaS2OffFaceGoodQuadraticMoment
    engelsmaS2OffFaceGoodQuadraticMoment
  rw [hk]
  dsimp [G, weight, Q, coeff, f, R, D, H, S, L, k, W,
    engelsmaS2OffFaceNaturalScale]
  rw [Finset.sum_div]
  change (∑ u ∈ G,
      weight u * (L * engelsmaS2CoordinateFiberFaceIntegral R m
        (engelsmaOffFaceExtension m u)) ^ 2 / (Q * L ^ 2)) =
    ∑ i : Fin 42, ∑ j : Fin 42,
      ∑ cp ∈ Finset.range (smallKExponentC i + 1),
        ∑ dp ∈ Finset.range (smallKExponentC j + 1),
          coeff i j cp dp * ((∑ u ∈ G, f i j cp dp u * weight u) / Q)
  have hRhs :
      (∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            coeff i j cp dp * ((∑ u ∈ G, f i j cp dp u * weight u) / Q)) =
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ∑ u ∈ G, coeff i j cp dp * (f i j cp dp u * weight u / Q) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro cp hcp
    apply Finset.sum_congr rfl
    intro dp hdp
    rw [Finset.sum_div, Finset.mul_sum]
  rw [hRhs]
  have hReorder :
      (∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ∑ u ∈ G, coeff i j cp dp * (f i j cp dp u * weight u / Q)) =
      ∑ u ∈ G, ∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            coeff i j cp dp * (f i j cp dp u * weight u / Q) := by
    calc
      _ = ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ u ∈ G, ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              coeff i j cp dp * (f i j cp dp u * weight u / Q) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro cp hcp
        exact Finset.sum_comm
      _ = ∑ i : Fin 42, ∑ j : Fin 42, ∑ u ∈ G,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              coeff i j cp dp * (f i j cp dp u * weight u / Q) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_comm
      _ = ∑ i : Fin 42, ∑ u ∈ G, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              coeff i j cp dp * (f i j cp dp u * weight u / Q) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ u ∈ G, ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              coeff i j cp dp * (f i j cp dp u * weight u / Q) :=
        Finset.sum_comm
  rw [hReorder]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := hpoint u hu
  rw [show (L * engelsmaS2CoordinateFiberFaceIntegral R m
      (engelsmaOffFaceExtension m u)) ^ 2 =
      L ^ 2 * engelsmaS2CoordinateFiberFaceIntegral R m
        (engelsmaOffFaceExtension m u) ^ 2 by ring]
  rw [hu']
  simp only [Finset.mul_sum]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro cp hcp
  apply Finset.sum_congr rfl
  intro dp hdp
  dsimp [coeff, f]
  field_simp [hL.ne', preSieveSingularSeries_pos D]

set_option maxRecDepth 9000 in
set_option maxHeartbeats 1400000 in
theorem tendsto_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m)
      atTop (nhds (
        ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
                  faceQuadraticIntegrand (engelsmaIndexEquiv m)
                    (smallKFaceInnerExponent i cp +
                      smallKFaceInnerExponent j dp) (cp + dp) t))) := by
  have hlim : Tendsto (fun N : ℕ =>
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFaceInnerCoefficient i cp *
              smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
              normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m
                (smallKFaceInnerExponent i cp +
                  smallKFaceInnerExponent j dp) (cp + dp))
      atTop (nhds (
        ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
                  faceQuadraticIntegrand (engelsmaIndexEquiv m)
                    (smallKFaceInnerExponent i cp +
                      smallKFaceInnerExponent j dp) (cp + dp) t))) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    apply tendsto_finsetSum Finset.univ
    intro j hj
    apply tendsto_finsetSum (Finset.range (smallKExponentC i + 1))
    intro cp hcp
    apply tendsto_finsetSum (Finset.range (smallKExponentC j + 1))
    intro dp hdp
    exact (tendsto_normalizedEngelsmaS2OffFaceGoodQuadraticMoment
      halpha m
        (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
        (cp + dp)).const_mul _
  apply hlim.congr'
  filter_upwards [
    eventually_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment_eq_monomialSum
      halpha m] with N hN
  exact hN.symm

set_option maxRecDepth 9000 in
theorem tendsto_normalizedEngelsmaS2CoordinateFiberGoodOuterMoment
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m)
      atTop (nhds (
        ∑ i : Fin 42, ∑ j : Fin 42,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
                  faceQuadraticIntegrand (engelsmaIndexEquiv m)
                    (smallKFaceInnerExponent i cp +
                      smallKFaceInnerExponent j dp) (cp + dp) t))) := by
  have hdiff :=
    tendsto_normalizedEngelsmaS2CoordinateFiberGoodOuterMoment_sub_complement_zero
      halpha m
  have hcomp :=
    tendsto_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
      halpha m
  have hsum := hdiff.add hcomp
  have h' := hsum.congr'
    (Eventually.of_forall (fun N => by ring))
  simpa using h'

end BoundedGaps.Maynard
