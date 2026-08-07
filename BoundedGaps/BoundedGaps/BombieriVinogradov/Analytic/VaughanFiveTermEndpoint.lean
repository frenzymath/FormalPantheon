import BoundedGaps.BombieriVinogradov.Analytic.RawPrimitiveMaxima
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermAggregate
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermSmallAggregate
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermLargeEnergy
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermEnergy

/-!
# Five-term Vaughan endpoint assembly

This file combines the exact twisted Vaughan identity with the corrected split
`-S3 = S3' + S3''` and lifts the resulting norm inequality to the raw
primitive-character endpoint maximum. It contains no weighted character
aggregation or cutoff optimization.

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 18--23, through the
five-term combination after equation (6.15). Semantic review: `SEM-459`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- A raw twisted von Mangoldt prefix is bounded by the corresponding
Chebyshev prefix. -/
theorem norm_twistedChebyshevSum_le_psi
    (y q : ℕ) (chi : DirichletCharacter ℂ q) :
    ‖twistedChebyshevSum y q chi‖ ≤ Chebyshev.psi y := by
  unfold twistedChebyshevSum
  calc
    ‖∑ n ∈ Finset.Icc 1 y,
        chi n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
        ∑ n ∈ Finset.Icc 1 y,
          ‖chi n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 y,
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (chi.norm_le_one n)
    _ = Chebyshev.psi y := by
      rw [Chebyshev.psi]
      simp only [Nat.floor_natCast]
      rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
        simpa using (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) y)]

/-- The raw primitive endpoint maximum is bounded by the untwisted Chebyshev
prefix at the same upper endpoint. -/
theorem primitiveRawEndpointMaximum_le_psi
    (x q : ℕ) (chi : primitiveCharacters q) :
    primitiveRawEndpointMaximum x q chi ≤ Chebyshev.psi x := by
  unfold primitiveRawEndpointMaximum
  split_ifs with hx
  · apply Finset.sup'_le
    intro y hy
    exact (norm_twistedChebyshevSum_le_psi y q chi.1).trans
      (Chebyshev.psi_mono (by
        exact_mod_cast (Finset.mem_Icc.mp hy).2))
  · exact Chebyshev.psi_nonneg x

/-- The corrected exact five-term Vaughan identity. The two pieces obtained
from the third term enter with minus signs because `-S3 = S3' + S3''`. -/
theorem twistedChebyshevSum_eq_vaughanFiveTerms
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (y q : ℕ) (chi : DirichletCharacter ℂ q) :
    twistedChebyshevSum y q chi =
      vaughanTwistedSumOne U y q chi +
      vaughanTwistedSumTwo V y q chi -
      vaughanTwistedSumThreeSmall U V y q chi -
      vaughanTwistedSumThreeLarge U V y q chi +
      vaughanTwistedSumFour U V y q chi := by
  rw [twistedChebyshevSum_eq_vaughanTwistedSums hU hV]
  have hthree :
      vaughanTwistedSumThree U V y q chi =
        -(vaughanTwistedSumThreeSmall U V y q chi +
          vaughanTwistedSumThreeLarge U V y q chi) := by
    rw [← neg_vaughanTwistedSumThree_eq_small_add_large hU hV]
    simp
  rw [hthree]
  ring

/-- Sum of the five nonnegative endpoint maxima arising from the corrected
signed Vaughan identity. -/
noncomputable def vaughanFiveTermEndpointMajorant
    (U V : ℝ) (x q : ℕ) (chi : DirichletCharacter ℂ q) : ℝ :=
  vaughanTwistedSumOneEndpointMaximum U x q chi +
    vaughanTwistedSumTwoEndpointMaximum V x q chi +
    vaughanTwistedSumThreeSmallEndpointMaximum U V x q chi +
    vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi +
    vaughanTwistedSumFourEndpointMaximum U V x q chi

/-- A raw primitive endpoint maximum over `2 ≤ y ≤ x` is bounded by the
five component maxima over the enlarged range `1 ≤ y ≤ x`. -/
theorem primitiveRawEndpointMaximum_le_vaughanFiveTermEndpointMajorant
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {x q : ℕ} (hx : 2 ≤ x) (chi : primitiveCharacters q) :
    primitiveRawEndpointMaximum x q chi ≤
      vaughanFiveTermEndpointMajorant U V x q chi.1 := by
  classical
  have hxOne : 1 ≤ x := by omega
  unfold primitiveRawEndpointMaximum
  rw [dif_pos hx]
  apply Finset.sup'_le
  intro y hy
  have hyBounds := Finset.mem_Icc.mp hy
  have hyComponent : y ∈ Finset.Icc 1 x :=
    Finset.mem_Icc.mpr ⟨by omega, hyBounds.2⟩
  have hOne :
      ‖vaughanTwistedSumOne U y q chi.1‖ ≤
        vaughanTwistedSumOneEndpointMaximum U x q chi.1 := by
    unfold vaughanTwistedSumOneEndpointMaximum
    rw [dif_pos hxOne]
    exact Finset.le_sup'
      (fun z ↦ ‖vaughanTwistedSumOne U z q chi.1‖) hyComponent
  have hTwo :
      ‖vaughanTwistedSumTwo V y q chi.1‖ ≤
        vaughanTwistedSumTwoEndpointMaximum V x q chi.1 := by
    unfold vaughanTwistedSumTwoEndpointMaximum
    rw [dif_pos hxOne]
    exact Finset.le_sup'
      (fun z ↦ ‖vaughanTwistedSumTwo V z q chi.1‖) hyComponent
  have hThreeSmall :
      ‖vaughanTwistedSumThreeSmall U V y q chi.1‖ ≤
        vaughanTwistedSumThreeSmallEndpointMaximum U V x q chi.1 := by
    unfold vaughanTwistedSumThreeSmallEndpointMaximum
    rw [dif_pos hxOne]
    exact Finset.le_sup'
      (fun z ↦ ‖vaughanTwistedSumThreeSmall U V z q chi.1‖) hyComponent
  have hThreeLarge :
      ‖vaughanTwistedSumThreeLarge U V y q chi.1‖ ≤
        vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1 := by
    unfold vaughanTwistedSumThreeLargeEndpointMaximum
    rw [dif_pos hxOne]
    exact Finset.le_sup'
      (fun z ↦ ‖vaughanTwistedSumThreeLarge U V z q chi.1‖) hyComponent
  have hFour :
      ‖vaughanTwistedSumFour U V y q chi.1‖ ≤
        vaughanTwistedSumFourEndpointMaximum U V x q chi.1 := by
    unfold vaughanTwistedSumFourEndpointMaximum
    rw [dif_pos hxOne]
    exact Finset.le_sup'
      (fun z ↦ ‖vaughanTwistedSumFour U V z q chi.1‖) hyComponent
  rw [twistedChebyshevSum_eq_vaughanFiveTerms hU hV]
  unfold vaughanFiveTermEndpointMajorant
  calc
    ‖vaughanTwistedSumOne U y q chi.1 +
        vaughanTwistedSumTwo V y q chi.1 -
        vaughanTwistedSumThreeSmall U V y q chi.1 -
        vaughanTwistedSumThreeLarge U V y q chi.1 +
        vaughanTwistedSumFour U V y q chi.1‖ ≤
      ‖vaughanTwistedSumOne U y q chi.1 +
          vaughanTwistedSumTwo V y q chi.1 -
          vaughanTwistedSumThreeSmall U V y q chi.1 -
          vaughanTwistedSumThreeLarge U V y q chi.1‖ +
        ‖vaughanTwistedSumFour U V y q chi.1‖ :=
      norm_add_le _ _
    _ ≤
      (‖vaughanTwistedSumOne U y q chi.1 +
          vaughanTwistedSumTwo V y q chi.1 -
          vaughanTwistedSumThreeSmall U V y q chi.1‖ +
        ‖vaughanTwistedSumThreeLarge U V y q chi.1‖) +
        ‖vaughanTwistedSumFour U V y q chi.1‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
      ((‖vaughanTwistedSumOne U y q chi.1 +
          vaughanTwistedSumTwo V y q chi.1‖ +
        ‖vaughanTwistedSumThreeSmall U V y q chi.1‖) +
        ‖vaughanTwistedSumThreeLarge U V y q chi.1‖) +
        ‖vaughanTwistedSumFour U V y q chi.1‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
      (((‖vaughanTwistedSumOne U y q chi.1‖ +
          ‖vaughanTwistedSumTwo V y q chi.1‖) +
        ‖vaughanTwistedSumThreeSmall U V y q chi.1‖) +
        ‖vaughanTwistedSumThreeLarge U V y q chi.1‖) +
        ‖vaughanTwistedSumFour U V y q chi.1‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ _ := by
      gcongr

end

end BoundedGaps.Maynard
