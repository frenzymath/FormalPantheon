import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.SieveAsymptotics.RoughSmoothTypeIBridge
import PrimesRestrictedDigits.TypeI.PropositionSevenOne

/-!
# Fundamental-sieve remainder and Type I progression error

This proves the exact reindex behind `q=d*e` in `MAYNARD-PRD-PUBLISHED`, pp. 153--154, Eq.
(7.6), and injects the corrected absolute remainder sum into Proposition 7.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact signed real summand controlled by published Proposition 7.1. -/
def realTypeIProgressionError
    (digit : Fin 10) (length q : Nat) : Real :=
  (((paddedRestrictedNumbers digit length).filter
      (fun n => q ∣ n ∧ n.Coprime 10)).card : Real) -
    (typeIProgressionDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real) / (q : Real)

/-- The exact weak-smooth inner modulus carrier in the small-parameter proof
of Maynard's Lemma 7.4. -/
def fundamentalSmoothModuli
    (X epsilon delta : Real) : Finset Nat := by
  classical
  exact (Finset.range (Nat.ceil (X ^ (epsilon / 2)))).filter fun e =>
    e.Coprime 10 ∧ weakSmoothPredicate (X ^ delta) e

@[simp] theorem mem_fundamentalSmoothModuli
    {X epsilon delta : Real} {e : Nat} :
    e ∈ fundamentalSmoothModuli X epsilon delta ↔
      (e : Real) < X ^ (epsilon / 2) ∧ e.Coprime 10 ∧
        weakSmoothPredicate (X ^ delta) e := by
  simp only [fundamentalSmoothModuli, Finset.mem_filter, Finset.mem_range,
    Nat.lt_ceil]

/-- The source-shaped count `#{a in A'_d : e | a}`. -/
def sourceSieveDivisorCount
    (digit : Fin 10) (length : Nat) (d e : PNat) : Nat :=
  ((sieveDilation
      ((paddedRestrictedNumbers digit length).filter
        (fun n => n.Coprime 10)) d).filter
    (fun a => (e : Nat) ∣ a)).card

/-- Divisibility inside `A'_d` is exactly the progression condition at
`q=d*e`; this requires two finite dilation reindexes. -/
theorem sourceSieveDivisorCount_eq_progressionCount
    (digit : Fin 10) (length : Nat) (d e : PNat) :
    sourceSieveDivisorCount digit length d e =
      ((paddedRestrictedNumbers digit length).filter
        (fun n => ((d : Nat) * (e : Nat)) ∣ n ∧ n.Coprime 10)).card := by
  rw [sourceSieveDivisorCount]
  rw [← card_sieveDilation_eq_card_filter_dvd
    (sieveDilation
      ((paddedRestrictedNumbers digit length).filter
        (fun n => n.Coprime 10)) d) e]
  rw [sieveDilation_mul, card_sieveDilation_eq_card_filter_dvd]
  simp only [PNat.mul_coe, Finset.filter_filter, and_comm]

/-- Maynard's signed source remainder `R_d(e)=count-main`. -/
def sourceSieveRemainder
    (digit : Fin 10) (length : Nat) (d e : PNat) : Real :=
  (sourceSieveDivisorCount digit length d e : Real) -
    (typeIProgressionDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real) /
        (((d : Nat) * (e : Nat) : Nat) : Real)

/-- The source remainder is exactly the signed Type I progression error at
the product modulus. -/
theorem sourceSieveRemainder_eq_realTypeIProgressionError
    (digit : Fin 10) (length : Nat) (d e : PNat) :
    sourceSieveRemainder digit length d e =
      realTypeIProgressionError digit length
        ((d : Nat) * (e : Nat)) := by
  rw [sourceSieveRemainder, sourceSieveDivisorCount_eq_progressionCount,
    realTypeIProgressionError]

/-- Rearranged defining equation `count=main+R_d(e)`. -/
theorem sourceSieveDivisorCount_cast_eq_main_add_remainder
    (digit : Fin 10) (length : Nat) (d e : PNat) :
    (sourceSieveDivisorCount digit length d e : Real) =
      (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (((d : Nat) * (e : Nat) : Nat) : Real) +
        sourceSieveRemainder digit length d e := by
  rw [sourceSieveRemainder]
  ring

/-- The corrected absolute double remainder sum injects into the exact Type I
modulus carrier. -/
theorem sum_abs_fundamentalRemainders_le_typeI
    (digit : Fin 10) (length : Nat) {X epsilon delta : Real}
    (hX : 0 < X) (hcutoff : 5 ≤ X ^ delta) :
    (∑ d ∈ maynardStrictRoughCarrier
        (X ^ (50 / 77 - epsilon)) (X ^ delta),
      ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
        |realTypeIProgressionError digit length (d * e)|) ≤
      ∑ q ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
        |realTypeIProgressionError digit length q| := by
  apply sum_rough_smooth_products_le_typeIModuliBelow
    (D := maynardStrictRoughCarrier
      (X ^ (50 / 77 - epsilon)) (X ^ delta))
    (E := fundamentalSmoothModuli X epsilon delta)
    (epsilon := epsilon)
    (f := fun q => |realTypeIProgressionError digit length q|)
    hX hcutoff
  · intro d hd
    exact (mem_maynardStrictRoughCarrier.mp hd).1
  · intro d hd
    exact (mem_maynardStrictRoughCarrier.mp hd).2.1
  · intro d hd
    exact (mem_maynardStrictRoughCarrier.mp hd).2.2
  · intro e he
    exact (mem_fundamentalSmoothModuli.mp he).1
  · intro e he
    exact (mem_fundamentalSmoothModuli.mp he).2.2
  · intro e he
    exact (mem_fundamentalSmoothModuli.mp he).2.1
  · intro q hq
    positivity

end

end PrimesRestrictedDigits
