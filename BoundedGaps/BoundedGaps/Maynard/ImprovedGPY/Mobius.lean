import BoundedGaps.Maynard.ImprovedGPY.MainTerm
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

noncomputable section

/-!
# Möbius indicator for cross-coordinate compatibility

Maynard2013v3, Section 5, in the proof of `lmm:S1Expression1` (source lines
305--313), removes the cross-coordinate coprimality restriction by inserting
one finite Möbius divisor sum for each ordered off-diagonal coordinate pair.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem sum_moebius_divisors_eq_one_iff
    (n : ℕ) :
    (∑ s ∈ n.divisors, ArithmeticFunction.moebius s) =
      if n = 1 then 1 else 0 := by
  calc
    (∑ s ∈ n.divisors, ArithmeticFunction.moebius s) =
        (ArithmeticFunction.moebius * ArithmeticFunction.zeta) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

def commonDivisorMoebiusSum (a b : ℕ) : ℝ :=
  ∑ s ∈ (Nat.gcd a b).divisors,
    (ArithmeticFunction.moebius s : ℝ)

theorem commonDivisorMoebiusSum_eq_coprime_indicator
    (a b : ℕ) :
    commonDivisorMoebiusSum a b = if Nat.Coprime a b then 1 else 0 := by
  unfold commonDivisorMoebiusSum
  have hsum := sum_moebius_divisors_eq_one_iff (Nat.gcd a b)
  have hsumR :
      (∑ s ∈ (Nat.gcd a b).divisors,
        (ArithmeticFunction.moebius s : ℝ)) =
        (if Nat.gcd a b = 1 then (1 : ℝ) else 0) := by
    exact_mod_cast hsum
  simpa only [Nat.coprime_iff_gcd_eq_one] using hsumR

def offDiagonalPairs (H : Finset ℕ) : Finset (H × H) :=
  Finset.univ.filter (fun ab => ab.1 ≠ ab.2)

theorem isCrossCoordinateCoprime_iff_ordered
    {H : Finset ℕ} {d e : H → ℕ} :
    IsCrossCoordinateCoprime H d e ↔
      ∀ {a b : H}, a ≠ b → Nat.Coprime (d a) (e b) := by
  constructor
  · intro h a b hab
    exact (h hab).1
  · intro h a b hab
    exact ⟨h hab, (h (Ne.symm hab)).symm⟩

def crossCoordinateMoebiusIndicator
    (H : Finset ℕ) (d e : H → ℕ) : ℝ :=
  ∏ ab ∈ offDiagonalPairs H,
    commonDivisorMoebiusSum (d ab.1) (e ab.2)

theorem crossCoordinateMoebiusIndicator_eq_compatibility_indicator
    (H : Finset ℕ) (d e : H → ℕ) :
    crossCoordinateMoebiusIndicator H d e =
      if IsCrossCoordinateCoprime H d e then 1 else 0 := by
  classical
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · simp only [hcross, if_true]
    unfold crossCoordinateMoebiusIndicator
    apply Finset.prod_eq_one
    intro ab hab
    rw [commonDivisorMoebiusSum_eq_coprime_indicator]
    rw [if_pos]
    exact (isCrossCoordinateCoprime_iff_ordered.mp hcross)
      (Finset.mem_filter.mp hab).2
  · simp only [hcross, if_false]
    have hnot := hcross
    rw [isCrossCoordinateCoprime_iff_ordered] at hnot
    push Not at hnot
    obtain ⟨a, b, hab, hcop⟩ := hnot
    unfold crossCoordinateMoebiusIndicator
    apply Finset.prod_eq_zero
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ (a, b), hab⟩
    · rw [commonDivisorMoebiusSum_eq_coprime_indicator, if_neg hcop]

def compatibleDivisorPairCommonDivisorTupleMobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    crossCoordinateMoebiusIndicator H d e *
      (∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorTupleTerm H d e u * (lambda d * lambda e))

theorem compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    compatibleDivisorPairCommonDivisorTupleSum H D lambda =
      compatibleDivisorPairCommonDivisorTupleMobiusSum H D lambda := by
  classical
  unfold compatibleDivisorPairCommonDivisorTupleSum
    compatibleDivisorPairCommonDivisorTupleMobiusSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [crossCoordinateMoebiusIndicator_eq_compatibility_indicator]
  by_cases hcross : IsCrossCoordinateCoprime H d e <;> simp [hcross]

def crossMoebiusTupleSupport
    (H : Finset ℕ) (d e : H → ℕ) :
    Finset (∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :=
  (offDiagonalPairs H).pi (fun ab =>
    (Nat.gcd (d ab.1) (e ab.2)).divisors)

def crossMoebiusTupleTerm
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  ∏ x ∈ (offDiagonalPairs H).attach,
    (ArithmeticFunction.moebius (s x.1 x.2) : ℝ)

theorem crossCoordinateMoebiusIndicator_eq_auxiliaryTupleSum
    (H : Finset ℕ) (d e : H → ℕ) :
    crossCoordinateMoebiusIndicator H d e =
      ∑ s ∈ crossMoebiusTupleSupport H d e,
        crossMoebiusTupleTerm H s := by
  classical
  unfold crossCoordinateMoebiusIndicator crossMoebiusTupleSupport
    crossMoebiusTupleTerm
  apply Finset.prod_sum

theorem mem_crossMoebiusTupleSupport_iff
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    s ∈ crossMoebiusTupleSupport H d e ↔
      ∀ (ab : H × H) (hab : ab ∈ offDiagonalPairs H),
        s ab hab ∣ d ab.1 ∧ s ab hab ∣ e ab.2 := by
  classical
  rw [crossMoebiusTupleSupport, Finset.mem_pi]
  constructor
  · intro hs ab hab
    exact Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp (hs ab hab)).1
  · intro hs ab hab
    apply Nat.mem_divisors.mpr
    refine ⟨Nat.dvd_gcd (hs ab hab).1 (hs ab hab).2, ?_⟩
    exact (Nat.gcd_pos_of_pos_left (e ab.2)
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree ab.1).ne_zero)).ne'

def compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    ∑ s ∈ crossMoebiusTupleSupport H d e,
      crossMoebiusTupleTerm H s *
        (∑ u ∈ commonDivisorTupleSupport H d e,
          commonDivisorTupleTerm H d e u * (lambda d * lambda e))

theorem compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    compatibleDivisorPairCommonDivisorTupleMobiusSum H D lambda =
      compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum H D lambda := by
  classical
  unfold compatibleDivisorPairCommonDivisorTupleMobiusSum
    compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [crossCoordinateMoebiusIndicator_eq_auxiliaryTupleSum]
  rw [Finset.sum_mul]

theorem compatibleDivisorPairMainSum_eq_commonDivisorTupleMobiusSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairMainSum H D W N lambda =
      (N : ℝ) / W *
        compatibleDivisorPairCommonDivisorTupleMobiusSum H D lambda := by
  rw [compatibleDivisorPairMainSum_eq_commonDivisorTupleSum hD]
  rw [compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum]

theorem sieveWeightSum_preSieved_eq_commonDivisorTupleMobiusSum_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      (N : ℝ) / W *
          compatibleDivisorPairCommonDivisorTupleMobiusSum H D lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  rw [sieveWeightSum_preSieved_eq_commonDivisorTupleSum_add_error
    hD hcoverage]
  rw [compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum]

theorem compatibleDivisorPairMainSum_eq_auxiliaryMobiusSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairMainSum H D W N lambda =
      (N : ℝ) / W *
        compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum H D lambda := by
  rw [compatibleDivisorPairMainSum_eq_commonDivisorTupleMobiusSum hD]
  rw [compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum]

theorem sieveWeightSum_preSieved_eq_auxiliaryMobiusSum_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N v : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      (N : ℝ) / W *
          compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum H D lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  rw [sieveWeightSum_preSieved_eq_commonDivisorTupleMobiusSum_add_error
    hD hcoverage]
  rw [compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum]

end BoundedGaps.Maynard
