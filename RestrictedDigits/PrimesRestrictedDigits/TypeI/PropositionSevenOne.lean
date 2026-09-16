import PrimesRestrictedDigits.Digits.LocalDensity
import PrimesRestrictedDigits.TypeI.BandReassembly

/-!
# Published Type I estimate

This rewrites the actual coprime-cardinality main term using the exact local density and
states published Proposition 7.1 in real absolute-value form.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The local constant `kappa` in published Proposition 7.1. -/
def typeIProgressionDensity (digit : Fin 10) : Rat :=
  (Nat.totient 10 : Rat) / 10 * restrictedDigitDensity digit

/-- The two source values of the Type I progression density. -/
theorem typeIProgressionDensity_eq (digit : Fin 10) :
    typeIProgressionDensity digit =
      if Nat.Coprime digit.val 10 then 1 / 3 else 4 / 9 := by
  have htotient : Nat.totient 10 = 4 := by decide
  rw [typeIProgressionDensity, restrictedDigitDensity_eq, htotient]
  by_cases hdigit : Nat.Coprime digit.val 10
  · simp only [if_pos hdigit]
    norm_num
  · simp only [if_neg hdigit]
    norm_num

/-- At positive decimal length, the actual coprime count is exactly the
published local density times the full restricted-digit count. -/
theorem card_coprime_paddedRestrictedNumbers_eq_density_mul_card
    (digit : Fin 10) {length : Nat} (hlength : 0 < length) :
    (((paddedRestrictedNumbers digit length).filter
      (fun n => Nat.Coprime n 10)).card : Rat) =
      typeIProgressionDensity digit *
        ((paddedRestrictedNumbers digit length).card : Rat) := by
  have hdensity :=
    ten_div_totient_mul_card_coprime_paddedRestrictedNumbers digit hlength
  have htotient : Nat.totient 10 = 4 := by decide
  rw [htotient] at hdensity
  rw [typeIProgressionDensity, htotient]
  norm_num at hdensity ⊢
  linear_combination (2 / 5 : Rat) * hdensity

/-- Complex-cast form used by the analytic progression estimate. -/
theorem card_coprime_paddedRestrictedNumbers_cast_complex
    (digit : Fin 10) {length : Nat} (hlength : 0 < length) :
    (((paddedRestrictedNumbers digit length).filter
      (fun n => Nat.Coprime n 10)).card : Complex) =
      (typeIProgressionDensity digit : Complex) *
        ((paddedRestrictedNumbers digit length).card : Complex) := by
  have hdensityCast := congrArg (fun x : Rat => (x : Complex))
    (card_coprime_paddedRestrictedNumbers_eq_density_mul_card digit hlength)
  simpa using hdensityCast

/-- Published Proposition 7.1 with the error retained as a complex norm. -/
theorem exists_sum_typeIProgressionError_le_densityMain
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
        Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * saving - 2) →
        (∑ q ∈ typeIModuliBelow Q,
          ‖(((paddedRestrictedNumbers digit length).filter
              (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
            (typeIProgressionDensity digit : Complex) *
              ((paddedRestrictedNumbers digit length).card : Complex) /
                (q : Complex)‖) ≤
          4 * (26400 * largeSieveConstant + 720) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  obtain ⟨lengthError, herror⟩ :=
    exists_sum_typeIProgressionError_le_coprimeMain saving hsaving
  refine ⟨max 1 lengthError, ?_⟩
  intro length hlength digit Q hQ
  have hlengthOne : 1 ≤ length :=
    (Nat.le_max_left 1 lengthError).trans hlength
  have hlengthError : lengthError ≤ length :=
    (Nat.le_max_right 1 lengthError).trans hlength
  have hdensity := card_coprime_paddedRestrictedNumbers_cast_complex digit
    (Nat.zero_lt_of_lt hlengthOne)
  simpa only [hdensity] using herror length hlengthError digit Q hQ

/-- Published Proposition 7.1 in its real absolute-value formulation. -/
theorem exists_typeIProgressionEstimate
    (saving : Real) (hsaving : 0 < saving) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (Q : Real),
        Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * saving - 2) →
        (∑ q ∈ typeIModuliBelow Q,
          |(((paddedRestrictedNumbers digit length).filter
              (fun n => q ∣ n ∧ n.Coprime 10)).card : Real) -
            (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (q : Real)|) ≤
          4 * (26400 * largeSieveConstant + 720) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := by
  obtain ⟨length0, hcomplex⟩ :=
    exists_sum_typeIProgressionError_le_densityMain saving hsaving
  refine ⟨length0, ?_⟩
  intro length hlength digit Q hQ
  have hbound := hcomplex length hlength digit Q hQ
  calc
    (∑ q ∈ typeIModuliBelow Q,
        |(((paddedRestrictedNumbers digit length).filter
            (fun n => q ∣ n ∧ n.Coprime 10)).card : Real) -
          (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (q : Real)|) =
        ∑ q ∈ typeIModuliBelow Q,
          ‖(((paddedRestrictedNumbers digit length).filter
              (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
            (typeIProgressionDensity digit : Complex) *
              ((paddedRestrictedNumbers digit length).card : Complex) /
                (q : Complex)‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hcast :
          (((((paddedRestrictedNumbers digit length).filter
              (fun n => q ∣ n ∧ n.Coprime 10)).card : Real) -
            (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (q : Real) : Real) : Complex) =
            (((paddedRestrictedNumbers digit length).filter
                (fun n => q ∣ n ∧ n.Coprime 10)).card : Complex) -
              (typeIProgressionDensity digit : Complex) *
                ((paddedRestrictedNumbers digit length).card : Complex) /
                  (q : Complex) := by
        norm_cast
      rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 4 * (26400 * largeSieveConstant + 720) *
        ((paddedRestrictedNumbers digit length).card : Real) *
          Real.log (((10 ^ length : Nat) : Real)) ^ (-saving) := hbound

end

end PrimesRestrictedDigits
