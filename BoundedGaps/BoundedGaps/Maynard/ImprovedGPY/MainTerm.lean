import BoundedGaps.Maynard.ImprovedGPY.PairSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Totient

noncomputable section

/-!
# LCM and totient expansion of the S1 main term

Maynard2013v3, Section 5, in the proof of `lmm:S1Expression1` (source lines
298--305), factors `N/W` from the compatible pair sum and expands every
inverse lcm by a finite common-divisor totient sum.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def compatibleDivisorPairNormalizedMainSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    (lambda d * lambda e) /
      ∏ h : H, (divisorTupleLcm H d e h : ℝ)

theorem compatibleDivisorPairMainSum_eq_factor_normalized
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {W N : ℕ} :
    compatibleDivisorPairMainSum H D W N lambda =
      (N : ℝ) / W * compatibleDivisorPairNormalizedMainSum H D lambda := by
  classical
  unfold compatibleDivisorPairMainSum compatibleDivisorPairNormalizedMainSum
    divisorPairModulus
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

def commonDivisorTotientSum (d e : ℕ) : ℝ :=
  ∑ u ∈ (Nat.gcd d e).divisors, (Nat.totient u : ℝ)

theorem commonDivisorTotientSum_eq_gcd (d e : ℕ) :
    commonDivisorTotientSum d e = (Nat.gcd d e : ℝ) := by
  unfold commonDivisorTotientSum
  exact_mod_cast Nat.sum_totient (Nat.gcd d e)

theorem inv_lcm_eq_commonDivisorTotientSum_div_mul
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ((Nat.lcm d e : ℕ) : ℝ)⁻¹ =
      commonDivisorTotientSum d e / ((d : ℝ) * e) := by
  rw [commonDivisorTotientSum_eq_gcd]
  have hlcm : (0 : ℝ) < Nat.lcm d e := by
    exact_mod_cast Nat.lcm_pos hd he
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hprod :
      (Nat.gcd d e : ℝ) * Nat.lcm d e = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  field_simp
  nlinarith

def compatibleDivisorPairTotientExpandedSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    (∏ h : H,
      commonDivisorTotientSum (d h) (e h) / ((d h : ℝ) * e h)) *
        (lambda d * lambda e)

theorem inverse_divisorTupleLcmProduct_eq_totientProduct
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) :
    ((∏ h : H, divisorTupleLcm H d e h : ℕ) : ℝ)⁻¹ =
      ∏ h : H,
        commonDivisorTotientSum (d h) (e h) / ((d h : ℝ) * e h) := by
  push_cast
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro h hh
  apply inv_lcm_eq_commonDivisorTotientSum_div_mul
  · exact Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero
  · exact Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero

theorem compatibleDivisorPairNormalizedMainSum_eq_totientExpanded
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairNormalizedMainSum H D lambda =
      compatibleDivisorPairTotientExpandedSum H D lambda := by
  classical
  unfold compatibleDivisorPairNormalizedMainSum
    compatibleDivisorPairTotientExpandedSum
  apply Finset.sum_congr rfl
  intro d hd_mem
  apply Finset.sum_congr rfl
  intro e he_mem
  have he_memD := (Finset.mem_filter.mp he_mem).1
  have hprod := inverse_divisorTupleLcmProduct_eq_totientProduct
    (hD d hd_mem) (hD e he_memD)
  push_cast at hprod
  rw [div_eq_mul_inv, hprod]
  ring

def commonDivisorTupleSupport
    (H : Finset ℕ) (d e : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset (fun h => (Nat.gcd (d h) (e h)).divisors)

def commonDivisorTupleTerm
    (H : Finset ℕ) (d e u : H → ℕ) : ℝ :=
  ∏ h : H, (Nat.totient (u h) : ℝ) / ((d h : ℝ) * e h)

def compatibleDivisorPairCommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    ∑ u ∈ commonDivisorTupleSupport H d e,
      commonDivisorTupleTerm H d e u * (lambda d * lambda e)

theorem totientProduct_eq_commonDivisorTupleSum
    (H : Finset ℕ) (d e : H → ℕ) :
    (∏ h : H, commonDivisorTotientSum (d h) (e h) /
      ((d h : ℝ) * e h)) =
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorTupleTerm H d e u := by
  classical
  unfold commonDivisorTupleSupport commonDivisorTupleTerm
  calc
    (∏ h : H, commonDivisorTotientSum (d h) (e h) /
      ((d h : ℝ) * e h)) =
        ∏ h : H, ∑ u ∈ (Nat.gcd (d h) (e h)).divisors,
          (Nat.totient u : ℝ) / ((d h : ℝ) * e h) := by
      apply Finset.prod_congr rfl
      intro h hh
      unfold commonDivisorTotientSum
      rw [Finset.sum_div]
    _ = ∑ u ∈ Fintype.piFinset
          (fun h : H => (Nat.gcd (d h) (e h)).divisors),
          ∏ h : H, (Nat.totient (u h) : ℝ) / ((d h : ℝ) * e h) :=
      Finset.prod_univ_sum _ _

theorem compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    compatibleDivisorPairTotientExpandedSum H D lambda =
      compatibleDivisorPairCommonDivisorTupleSum H D lambda := by
  classical
  unfold compatibleDivisorPairTotientExpandedSum
    compatibleDivisorPairCommonDivisorTupleSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e _he
  rw [totientProduct_eq_commonDivisorTupleSum]
  rw [Finset.sum_mul]

theorem mem_commonDivisorTupleSupport_iff
    {H : Finset ℕ} {R W : ℕ} {d e u : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    u ∈ commonDivisorTupleSupport H d e ↔
      ∀ h : H, u h ∣ d h ∧ u h ∣ e h := by
  classical
  rw [commonDivisorTupleSupport, Fintype.mem_piFinset]
  constructor
  · intro hu h
    exact Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp (hu h)).1
  · intro hu h
    apply Nat.mem_divisors.mpr
    refine ⟨Nat.dvd_gcd (hu h).1 (hu h).2, ?_⟩
    exact (Nat.gcd_pos_of_pos_left (e h)
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)).ne'

theorem compatibleDivisorPairMainSum_eq_totientExpanded
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairMainSum H D W N lambda =
      (N : ℝ) / W * compatibleDivisorPairTotientExpandedSum H D lambda := by
  rw [compatibleDivisorPairMainSum_eq_factor_normalized]
  rw [compatibleDivisorPairNormalizedMainSum_eq_totientExpanded hD]

theorem compatibleDivisorPairMainSum_eq_commonDivisorTupleSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairMainSum H D W N lambda =
      (N : ℝ) / W *
        compatibleDivisorPairCommonDivisorTupleSum H D lambda := by
  rw [compatibleDivisorPairMainSum_eq_totientExpanded hD]
  rw [compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum]

theorem sieveWeightSum_preSieved_eq_totientExpanded_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      (N : ℝ) / W * compatibleDivisorPairTotientExpandedSum H D lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  rw [sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error
    hD hcoverage]
  rw [compatibleDivisorPairMainSum_eq_totientExpanded hD]

theorem sieveWeightSum_preSieved_eq_commonDivisorTupleSum_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      (N : ℝ) / W *
          compatibleDivisorPairCommonDivisorTupleSum H D lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  rw [sieveWeightSum_preSieved_eq_totientExpanded_add_error hD hcoverage]
  rw [compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum]

theorem abs_sieveWeightSum_preSieved_sub_totientExpanded_le_coefficientMass
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) (hW : 0 < W) :
    |sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) -
        (N : ℝ) / W * compatibleDivisorPairTotientExpandedSum H D lambda| ≤
      compatibleDivisorPairCoefficientMass H D lambda := by
  rw [← compatibleDivisorPairMainSum_eq_totientExpanded hD]
  exact abs_sieveWeightSum_preSieved_sub_main_le_coefficientMass
    hD hcoverage hW

theorem abs_sieveWeightSum_preSieved_sub_totientExpanded_le_card_sq_mul
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ} {L : ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) (hW : 0 < W)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    |sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) -
        (N : ℝ) / W * compatibleDivisorPairTotientExpandedSum H D lambda| ≤
      (D.card : ℝ)^2 * L^2 := by
  rw [← compatibleDivisorPairMainSum_eq_totientExpanded hD]
  exact abs_sieveWeightSum_preSieved_sub_main_le_card_sq_mul
    hD hcoverage hW hL hbound

end BoundedGaps.Maynard
