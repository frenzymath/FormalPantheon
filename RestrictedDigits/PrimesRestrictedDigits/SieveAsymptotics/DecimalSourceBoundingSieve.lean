import PrimesRestrictedDigits.SieveAsymptotics.DecimalSievePrimeProduct
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import Mathlib.NumberTheory.SelbergSieve

/-!
# Bounding sieve for the decimal source set

This packages Maynard's dilated coprime digit carrier as Mathlib's `BoundingSieve` and
identifies its finite sums with the source divisor count and remainder.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The global reciprocal local-density arithmetic function. -/
def reciprocalArithmeticFunction : ArithmeticFunction Real :=
  ⟨fun n => (n : Real)⁻¹, by simp⟩

@[simp] theorem reciprocalArithmeticFunction_apply (n : Nat) :
    reciprocalArithmeticFunction n = (n : Real)⁻¹ := rfl

theorem reciprocalArithmeticFunction_isMultiplicative :
    reciprocalArithmeticFunction.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [reciprocalArithmeticFunction_apply, Nat.cast_mul]
    rw [mul_inv_rev, mul_comm]

/-- The exact `BoundingSieve` attached to Maynard's source set `A'_d`. -/
def sourceBoundingSieve
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) : BoundingSieve where
  support := sieveDilation
    ((paddedRestrictedNumbers digit length).filter fun n => n.Coprime 10) d
  prodPrimes := decimalSievePrimeProduct z
  prodPrimes_squarefree := squarefree_decimalSievePrimeProduct z
  weights := fun _ => 1
  weights_nonneg := by intro; norm_num
  totalMass := (typeIProgressionDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real) / (d : Real)
  nu := reciprocalArithmeticFunction
  nu_mult := reciprocalArithmeticFunction_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

@[simp] theorem sourceBoundingSieve_support
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    (sourceBoundingSieve digit length d z).support =
      sieveDilation
        ((paddedRestrictedNumbers digit length).filter
          fun n => n.Coprime 10) d := rfl

@[simp] theorem sourceBoundingSieve_prodPrimes
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    (sourceBoundingSieve digit length d z).prodPrimes =
      decimalSievePrimeProduct z := rfl

@[simp] theorem sourceBoundingSieve_weights
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) (n : Nat) :
    (sourceBoundingSieve digit length d z).weights n = 1 := rfl

@[simp] theorem sourceBoundingSieve_totalMass
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    (sourceBoundingSieve digit length d z).totalMass =
      (typeIProgressionDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / (d : Real) := rfl

theorem sourceBoundingSieve_totalMass_nonneg
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    0 <= (sourceBoundingSieve digit length d z).totalMass := by
  have hDensity : 0 <= (typeIProgressionDensity digit : Real) := by
    rw [typeIProgressionDensity_eq]
    split_ifs <;> norm_num
  rw [sourceBoundingSieve_totalMass]
  positivity

theorem sourceBoundingSieve_nu_eq_reciprocal
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    ((sourceBoundingSieve digit length d z).nu : Nat -> Real) =
      fun n : Nat => (n : Real)⁻¹ := by
  rfl

theorem sourceBoundingSieve_multSum_eq
    (digit : Fin 10) (length : Nat) (d e : PNat) (z : Real) :
    (sourceBoundingSieve digit length d z).multSum e =
      (sourceSieveDivisorCount digit length d e : Real) := by
  simp [BoundingSieve.multSum, sourceBoundingSieve,
    sourceSieveDivisorCount]

theorem sourceBoundingSieve_rem_eq
    (digit : Fin 10) (length : Nat) (d e : PNat) (z : Real) :
    (sourceBoundingSieve digit length d z).rem e =
      sourceSieveRemainder digit length d e := by
  rw [BoundingSieve.rem, sourceBoundingSieve_multSum_eq,
    sourceSieveRemainder]
  simp only [sourceBoundingSieve, reciprocalArithmeticFunction_apply,
    Nat.cast_mul]
  have hd : (d : Real) ≠ 0 := by positivity
  have he : (e : Real) ≠ 0 := by positivity
  field_simp

private theorem coprime_ten_of_mem_sourceBoundingSieveSupport
    (digit : Fin 10) (length : Nat) (d : PNat) {n : Nat}
    (hn : n ∈ sieveDilation
      ((paddedRestrictedNumbers digit length).filter
        fun a => a.Coprime 10) d) :
    n.Coprime 10 := by
  have hnFilter := Finset.mem_filter.mp (mem_sieveDilation.mp hn)
  exact (Nat.coprime_mul_iff_left.mp hnFilter.2).1

theorem sourceBoundingSieve_siftedSum_eq_card
    (digit : Fin 10) (length : Nat) (d : PNat) {z : Real}
    (_hz : 5 <= z) :
    (sourceBoundingSieve digit length d z).siftedSum =
      ((strictSiftedCarrier
        (sieveDilation
          ((paddedRestrictedNumbers digit length).filter
            fun n => n.Coprime 10) d) z).card : Real) := by
  let C := sieveDilation
    ((paddedRestrictedNumbers digit length).filter fun n => n.Coprime 10) d
  have hfilter :
      C.filter (fun n => (decimalSievePrimeProduct z).Coprime n) =
        strictSiftedCarrier C z := by
    ext n
    rw [Finset.mem_filter, mem_strictSiftedCarrier]
    constructor
    · rintro ⟨hnC, hnProduct⟩
      have hnTen : n.Coprime 10 :=
        coprime_ten_of_mem_sourceBoundingSieveSupport digit length d hnC
      exact ⟨hnC,
        (coprime_decimalSievePrimeProduct_iff_strictRoughPredicate hnTen).mp
          hnProduct⟩
    · rintro ⟨hnC, hnRough⟩
      have hnTen : n.Coprime 10 :=
        coprime_ten_of_mem_sourceBoundingSieveSupport digit length d hnC
      exact ⟨hnC,
        (coprime_decimalSievePrimeProduct_iff_strictRoughPredicate hnTen).mpr
          hnRough⟩
  change (∑ n ∈ C,
    if (decimalSievePrimeProduct z).Coprime n then 1 else 0) = _
  rw [Finset.sum_boole, hfilter]

end

end PrimesRestrictedDigits
