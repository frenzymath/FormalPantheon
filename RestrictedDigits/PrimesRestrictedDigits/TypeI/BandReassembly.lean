import PrimesRestrictedDigits.TypeI.LargeBandAggregation
import PrimesRestrictedDigits.TypeI.SmallBandAggregation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reassembly of the Type I band estimates

This joins the small and large normalized branches, returns through the exact harmonic and
decimal-fiber reductions, and bounds the progression error with its actual coprime-cardinality
main term.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The harmonic reduced-error bound rewritten on the exact active equality
fibers. -/
theorem sum_typeIReducedErrorFourierSum_div_le_activeBands
    (digit : Fin 10) (length : Nat) (Q : Real) :
    (∑ q ∈ typeIModuliBelow Q,
      typeIReducedErrorFourierSum digit length q / (q : Real)) ≤
      (harmonic (Nat.ceil Q - 1) : Real) *
        ∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeIDecadeScalesBelow Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real) := by
  calc
    (∑ q ∈ typeIModuliBelow Q,
        typeIReducedErrorFourierSum digit length q / (q : Real)) ≤
        (harmonic (Nat.ceil Q - 1) : Real) *
          ∑ d ∈ Nat.divisors 10,
            ∑ q ∈ (Finset.range (Nat.ceil Q)).filter
                (fun q => 1 < q ∧ q.Coprime 10),
              typeIReducedFrequencyMass digit length d q / (q : Real) :=
      sum_typeIReducedErrorFourierSum_div_le_harmonic digit length Q
    _ = (harmonic (Nat.ceil Q - 1) : Real) *
        ∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeIDecadeScalesBelow Q,
            ∑ q ∈ typeIDecadeFiber Q R,
              typeIReducedFrequencyMass digit length d q / (q : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      change (∑ q ∈ typeIReducedDenominatorsBelow Q,
          typeIReducedFrequencyMass digit length d q / (q : Real)) = _
      exact (sum_typeIDecadeFiber Q
        (fun q => typeIReducedFrequencyMass digit length d q / (q : Real))).symm

/-- The two completed band branches give the full normalized Type I
harmonic-fiber estimate. -/
theorem exists_harmonic_mul_sum_typeIBands_le
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
        Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * saving - 2) →
        (harmonic (Nat.ceil Q - 1) : Real) *
            ∑ d ∈ Nat.divisors 10,
              ∑ R ∈ typeIDecadeScalesBelow Q,
                ∑ q ∈ typeIDecadeFiber Q R,
                  typeIReducedFrequencyMass digit length d q / (q : Real) ≤
          (26400 * largeSieveConstant + 720) *
            Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  obtain ⟨lengthSmall, hsmall⟩ :=
    exists_harmonic_mul_sum_smallTypeIBands_le saving hsaving
  refine ⟨max 1 lengthSmall, ?_⟩
  intro length hlength digit Q hQ
  have hlengthOne : 1 ≤ length :=
    (Nat.le_max_left 1 lengthSmall).trans hlength
  have hlengthSmall : lengthSmall ≤ length :=
    (Nat.le_max_right 1 lengthSmall).trans hlength
  have hsmallAt := hsmall length hlengthSmall digit Q hQ
  have hlargeAt := harmonic_mul_sum_largeTypeIBands_le saving digit length Q
    hsaving hlengthOne hQ
  let H : Real := harmonic (Nat.ceil Q - 1)
  let P : Real := Real.log (((10 ^ length : Nat) : Real)) ^ (-saving)
  let w : Nat → Real → Real := fun d R =>
    ∑ q ∈ typeIDecadeFiber Q R,
      typeIReducedFrequencyMass digit length d q / (q : Real)
  have hsplit :
      (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeISmallDecadeScales saving length Q, w d R) +
        (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeILargeDecadeScales saving length Q, w d R) =
        ∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeIDecadeScalesBelow Q, w d R := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact sum_typeISmallDecadeScales_add_sum_typeILargeDecadeScales
      saving length Q (w d)
  change H * (∑ d ∈ Nat.divisors 10,
      ∑ R ∈ typeIDecadeScalesBelow Q, w d R) ≤
    (26400 * largeSieveConstant + 720) * P
  calc
    H * (∑ d ∈ Nat.divisors 10,
        ∑ R ∈ typeIDecadeScalesBelow Q, w d R) =
        H * ((∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeISmallDecadeScales saving length Q, w d R) +
          ∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeILargeDecadeScales saving length Q, w d R) := by
      rw [hsplit]
    _ = H * (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeISmallDecadeScales saving length Q, w d R) +
        H * (∑ d ∈ Nat.divisors 10,
          ∑ R ∈ typeILargeDecadeScales saving length Q, w d R) := by ring
    _ ≤ 720 * P + 26400 * largeSieveConstant * P :=
      add_le_add hsmallAt hlargeAt
    _ = (26400 * largeSieveConstant + 720) * P := by ring

/-- Any bound for the normalized active-band sum gives a progression-count
bound with the separate corrected denominator-reduction factor four. -/
theorem sum_typeIProgressionError_le_of_activeBandBound
    (digit : Fin 10) (length : Nat) (Q B : Real)
    (hbands :
      (harmonic (Nat.ceil Q - 1) : Real) *
          ∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeIDecadeScalesBelow Q,
              ∑ q ∈ typeIDecadeFiber Q R,
                typeIReducedFrequencyMass digit length d q / (q : Real) ≤ B) :
    (∑ q ∈ typeIModuliBelow Q,
      ‖(((paddedRestrictedNumbers digit length).filter
          (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
        (((paddedRestrictedNumbers digit length).filter
          (fun n => n.Coprime 10)).card : Complex) / (q : Complex)‖) ≤
      4 * ((paddedRestrictedNumbers digit length).card : Real) * B := by
  have hA : 0 ≤ ((paddedRestrictedNumbers digit length).card : Real) := by
    positivity
  calc
    (∑ q ∈ typeIModuliBelow Q,
        ‖(((paddedRestrictedNumbers digit length).filter
            (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
          (((paddedRestrictedNumbers digit length).filter
            (fun n => n.Coprime 10)).card : Complex) / (q : Complex)‖) ≤
        ∑ q ∈ typeIModuliBelow Q,
          4 * (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
            typeIReducedErrorFourierSum digit length q := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_typeIProgressionCount_sub_coprimeMain_le digit length q
        (Finset.mem_filter.mp hq).2
    _ = 4 * ((paddedRestrictedNumbers digit length).card : Real) *
        ∑ q ∈ typeIModuliBelow Q,
          typeIReducedErrorFourierSum digit length q / (q : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ 4 * ((paddedRestrictedNumbers digit length).card : Real) *
        ((harmonic (Nat.ceil Q - 1) : Real) *
          ∑ d ∈ Nat.divisors 10,
            ∑ R ∈ typeIDecadeScalesBelow Q,
              ∑ q ∈ typeIDecadeFiber Q R,
                typeIReducedFrequencyMass digit length d q / (q : Real)) := by
      apply mul_le_mul_of_nonneg_left
        (sum_typeIReducedErrorFourierSum_div_le_activeBands digit length Q)
      positivity
    _ ≤ 4 * ((paddedRestrictedNumbers digit length).card : Real) * B :=
      mul_le_mul_of_nonneg_left hbands (mul_nonneg (by norm_num) hA)

/-- The completed analytic Type I estimate with the exact actual-coprime-card
main term. The next density bridge rewrites that card to the published
piecewise constant. -/
theorem exists_sum_typeIProgressionError_le_coprimeMain
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
        Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * saving - 2) →
        (∑ q ∈ typeIModuliBelow Q,
          ‖(((paddedRestrictedNumbers digit length).filter
              (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
            (((paddedRestrictedNumbers digit length).filter
              (fun n => n.Coprime 10)).card : Complex) / (q : Complex)‖) ≤
          4 * (26400 * largeSieveConstant + 720) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  obtain ⟨length0, hbands⟩ :=
    exists_harmonic_mul_sum_typeIBands_le saving hsaving
  refine ⟨length0, ?_⟩
  intro length hlength digit Q hQ
  have hbound := sum_typeIProgressionError_le_of_activeBandBound
    digit length Q
      ((26400 * largeSieveConstant + 720) *
        Real.log (((10 ^ length : Nat) : Real)) ^ (-saving))
      (hbands length hlength digit Q hQ)
  calc
    (∑ q ∈ typeIModuliBelow Q,
        ‖(((paddedRestrictedNumbers digit length).filter
            (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
          (((paddedRestrictedNumbers digit length).filter
            (fun n => n.Coprime 10)).card : Complex) / (q : Complex)‖) ≤
        4 * ((paddedRestrictedNumbers digit length).card : Real) *
          ((26400 * largeSieveConstant + 720) *
            Real.log (((10 ^ length : Nat) : Real)) ^ (-saving)) := hbound
    _ = 4 * (26400 * largeSieveConstant + 720) *
        ((paddedRestrictedNumbers digit length).card : Real) *
          Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by ring

end

end PrimesRestrictedDigits
