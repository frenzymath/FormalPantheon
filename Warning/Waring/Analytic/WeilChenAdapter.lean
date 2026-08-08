import Waring.Analytic.ChenFourPrimeField
import Waring.Analytic.ChenFive
import Waring.Analytic.WeilPrimeFieldBound

/-!
# Adapter from the pure additive Weil bound to Chen's prime-field input

Chen lists coefficients from degree five down to degree one, whereas the
Artin construction indexes them from degree one upward.  Reversing the five
coefficients identifies the phase sums.  Selecting the highest nonzero
coefficient then applies the Weil estimate with a factor at most four.
 -/

namespace Waring.Analytic

open scoped BigOperators

/-- Chen's coefficient list, reindexed by ascending positive exponent. -/
def fifthPointPhaseCoefficients {R : Type*}
    (a₀ a₁ a₂ a₃ a₄ : R) : Fin 5 → R := fun i ↦
  match i.val with
  | 0 => a₄
  | 1 => a₃
  | 2 => a₂
  | 3 => a₁
  | _ => a₀

/-- The ascending point phase is exactly Chen's descending-coefficient
polynomial phase. -/
theorem pointPhase_fifthPointPhaseCoefficients
    {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ x : R) :
    Weil.pointPhase (fifthPointPhaseCoefficients a₀ a₁ a₂ a₃ a₄) x =
      fifthPolynomial a₀ a₁ a₂ a₃ a₄ x := by
  rw [Weil.pointPhase]
  simp [Fin.sum_univ_succ, fifthPointPhaseCoefficients, fifthPolynomial]
  ring

/-- For primes above five, the pure additive Weil bound supplies Chen's
uniform `5 * sqrt p` prime-field hypothesis. -/
theorem chenFourPrimeFieldSquareRootBound_of_five_lt
    (p : Nat) [Fact p.Prime] [NeZero p] (hp : 5 < p) :
    ChenFourPrimeFieldSquareRootBound p := by
  intro a₀ a₁ a₂ a₃ a₄ hcoeff
  let b : Fin 5 → ZMod p := fifthPointPhaseCoefficients
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
      (a₃ : ZMod p) (a₄ : ZMod p)
  have hsum :
      integerPolynomialCompleteSum (q := p) a₀ a₁ a₂ a₃ a₄ =
        ∑ x : ZMod p, ZMod.stdAddChar (Weil.pointPhase b x) := by
    rw [integerPolynomialCompleteSum, polynomialCompleteSum]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact (pointPhase_fifthPointPhaseCoefficients
      (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
        (a₃ : ZMod p) (a₄ : ZMod p) x).symm
  have hsqrt : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
  by_cases h₀ : (a₀ : ZMod p) ≠ 0
  · have hweil := Weil.norm_pointPhase_sum_le
      (p := p) (d := 5) (by omega) (by omega) (by omega) b (by omega)
        (by simpa [b, fifthPointPhaseCoefficients] using h₀)
        (by intro i hi; omega)
    rw [hsum]
    norm_num at hweil ⊢
    nlinarith
  · have h₀zero : (a₀ : ZMod p) = 0 := not_ne_iff.mp h₀
    by_cases h₁ : (a₁ : ZMod p) ≠ 0
    · have hweil := Weil.norm_pointPhase_sum_le
        (p := p) (d := 4) (by omega) (by omega) (by omega) b (by omega)
          (by simpa [b, fifthPointPhaseCoefficients] using h₁)
          (by
            intro i hi
            fin_cases i <;>
              simp_all [b, fifthPointPhaseCoefficients])
      rw [hsum]
      norm_num at hweil ⊢
      nlinarith
    · have h₁zero : (a₁ : ZMod p) = 0 := not_ne_iff.mp h₁
      by_cases h₂ : (a₂ : ZMod p) ≠ 0
      · have hweil := Weil.norm_pointPhase_sum_le
          (p := p) (d := 3) (by omega) (by omega) (by omega) b (by omega)
            (by simpa [b, fifthPointPhaseCoefficients] using h₂)
            (by
              intro i hi
              fin_cases i <;>
                simp_all [b, fifthPointPhaseCoefficients])
        rw [hsum]
        norm_num at hweil ⊢
        nlinarith
      · have h₂zero : (a₂ : ZMod p) = 0 := not_ne_iff.mp h₂
        by_cases h₃ : (a₃ : ZMod p) ≠ 0
        · have hweil := Weil.norm_pointPhase_sum_le
            (p := p) (d := 2) (by omega) (by omega) (by omega) b (by omega)
              (by simpa [b, fifthPointPhaseCoefficients] using h₃)
              (by
                intro i hi
                fin_cases i <;>
                  simp_all [b, fifthPointPhaseCoefficients])
          rw [hsum]
          norm_num at hweil ⊢
          nlinarith
        · have h₃zero : (a₃ : ZMod p) = 0 := not_ne_iff.mp h₃
          have h₄ : (a₄ : ZMod p) ≠ 0 := by
            rcases hcoeff with h | h | h | h | h
            · exact (h h₀zero).elim
            · exact (h h₁zero).elim
            · exact (h h₂zero).elim
            · exact (h h₃zero).elim
            · exact h
          have hweil := Weil.norm_pointPhase_sum_le
            (p := p) (d := 1) (by omega) (by omega) (by omega) b (by omega)
              (by simpa [b, fifthPointPhaseCoefficients] using h₄)
              (by
                intro i hi
                fin_cases i <;>
                  simp_all [b, fifthPointPhaseCoefficients])
          rw [hsum]
          calc
            ‖∑ x : ZMod p, ZMod.stdAddChar (Weil.pointPhase b x)‖ ≤ 0 := by
              simpa using hweil
            _ ≤ 5 * Real.sqrt (p : Real) := by positivity

/-- The large-prime hypothesis consumed by Chen's Lemma 5 is unconditional. -/
theorem chenFiveLargePrimeFieldBound : ChenFiveLargePrimeFieldBound := by
  intro p hp hpLarge
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact chenFourPrimeFieldBound_of_squareRootBound p
    (chenFourPrimeFieldSquareRootBound_of_five_lt p (by omega))

end Waring.Analytic
