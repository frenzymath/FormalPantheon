import PrimesRestrictedDigits.SieveDecomposition.Definitions
import PrimesRestrictedDigits.SieveAsymptotics.DecimalSievePrimeProduct
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Coprime ambient bounding sieve

This is the finite ambient carrier used in Maynard's Eq. (7.8).  The
progression estimate here is elementary: coprime residues are periodic modulo
ten, and the only loss from a half-open real endpoint is a bounded terminal
block.  The quantitative aggregate is owned by a later module.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.4, p. 155, Eq. (7.8).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Maynard's ambient interval with the two non-coprime decimal residues
removed.  The interval itself still contains zero; the filter removes it. -/
def maynardCoprimeAmbientCarrier (X : Real) : Finset Nat :=
  (maynardAmbientCarrier X).filter (fun n => n.Coprime 10)

@[simp] theorem mem_maynardCoprimeAmbientCarrier {X : Real} {n : Nat} :
    n ∈ maynardCoprimeAmbientCarrier X ↔
      (n : Real) < X ∧ n.Coprime 10 := by
  simp [maynardCoprimeAmbientCarrier]

theorem maynardAmbientCarrier_natCast (N : Nat) :
    maynardAmbientCarrier (N : Real) = Finset.range N := by
  ext n
  simp only [mem_maynardAmbientCarrier, Finset.mem_range]
  exact_mod_cast (show n < N ↔ n < N from Iff.rfl)

theorem maynardCoprimeAmbientCarrier_natCast (N : Nat) :
    maynardCoprimeAmbientCarrier (N : Real) =
      (Finset.range N).filter (fun n => n.Coprime 10) := by
  rw [maynardCoprimeAmbientCarrier, maynardAmbientCarrier_natCast]

theorem maynardCoprimeAmbientCarrier_eq_filter_range_ceil (X : Real) :
    maynardCoprimeAmbientCarrier X =
      (Finset.range (Nat.ceil X)).filter (fun n => n.Coprime 10) := by
  ext n
  simp [maynardCoprimeAmbientCarrier, maynardAmbientCarrier,
    naturalLeftClosedRightOpenInterval]

@[simp] theorem card_maynardAmbientCarrier_natCast (N : Nat) :
    (maynardAmbientCarrier (N : Real)).card = N := by
  rw [maynardAmbientCarrier_natCast]
  simp

private theorem coprimeTen_periodic :
    Function.Periodic (fun n : Nat => n.Coprime 10) 10 := by
  intro n
  simp [Nat.coprime_comm]

private theorem coprimeTen_count_block :
    Nat.count (fun n : Nat => n.Coprime 10) 10 = 4 := by
  rw [Nat.count_eq_card_filter_range]
  decide

private theorem coprimeTen_count_mul (m : Nat) :
    Nat.count (fun n : Nat => n.Coprime 10) (10 * m) = 4 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Nat.count_add, ih]
      have hshift :
          (fun k : Nat => (10 * m + k).Coprime 10) =
            (fun k : Nat => k.Coprime 10) := by
        funext k
        simpa only [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using
          (coprimeTen_periodic.nsmul m k)
      have hshiftCount :
          Nat.count (fun k : Nat => (10 * m + k).Coprime 10) 10 =
            Nat.count (fun k : Nat => k.Coprime 10) 10 := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        apply congrArg Finset.card
        ext k
        simp
      rw [hshiftCount, coprimeTen_count_block]
      ring

private theorem coprimeTen_count_terminal (a r : Nat) :
    0 <= Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r ∧
      Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r <= r := by
  exact ⟨Nat.zero_le _, @Nat.count_le (fun n : Nat => (10 * a + n).Coprime 10) _ r⟩

private theorem coprimeTen_count_real_error (M : Nat) :
    |(Nat.count (fun n : Nat => n.Coprime 10) M : Real) -
        (2 / 5 : Real) * (M : Real)| <= 9 := by
  let a : Nat := M / 10
  let r : Nat := M % 10
  have hdecomp : M = 10 * a + r := by
    dsimp [a, r]
    omega
  have hcount :
      Nat.count (fun n : Nat => n.Coprime 10) M =
        4 * a + Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r := by
    rw [hdecomp, Nat.count_add, coprimeTen_count_mul]
  have hterminal := coprimeTen_count_terminal a r
  have hcountCast :
      (Nat.count (fun n : Nat => n.Coprime 10) M : Real) =
        4 * (a : Real) +
          (Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r : Real) := by
    exact_mod_cast hcount
  have hdecompCast : (M : Real) = 10 * (a : Real) + (r : Real) := by
    exact_mod_cast hdecomp
  have hr : (r : Real) < 10 := by
    exact_mod_cast (Nat.mod_lt M (by norm_num : 0 < (10 : Nat)))
  have hterminalNonneg :
      0 <= (Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r : Real) := by
    exact_mod_cast hterminal.1
  have hterminalLe :
      (Nat.count (fun n : Nat => (10 * a + n).Coprime 10) r : Real) <= (r : Real) := by
    exact_mod_cast hterminal.2
  rw [hcountCast, hdecompCast]
  rw [abs_le]
  constructor <;> nlinarith

/-- The coprime ambient carrier at an integral power of ten has the exact
cardinality `4 * 10^(length-1)`. -/
theorem card_maynardCoprimeAmbientCarrier_powerTen
    {length : Nat} (hlength : 0 < length) :
      (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card =
      4 * 10 ^ (length - 1) := by
  rw [maynardCoprimeAmbientCarrier_natCast]
  have hcount := coprimeTen_count_mul (10 ^ (length - 1))
  have hpow : 10 ^ length = 10 * 10 ^ (length - 1) := by
    calc
      10 ^ length = 10 ^ (length - 1 + 1) := by
        rw [Nat.sub_add_cancel hlength]
      _ = 10 ^ (length - 1) * 10 := by rw [Nat.pow_succ]
      _ = 10 * 10 ^ (length - 1) := by ring
  calc
    ((Finset.range (10 ^ length)).filter (fun n => n.Coprime 10)).card =
        Nat.count (fun n => n.Coprime 10) (10 ^ length) := by
          exact (Nat.count_eq_card_filter_range
            (fun n : Nat => n.Coprime 10) _).symm
    _ = Nat.count (fun n => n.Coprime 10) (10 * 10 ^ (length - 1)) := by rw [hpow]
    _ = 4 * 10 ^ (length - 1) := hcount

theorem card_maynardCoprimeAmbientCarrier_powerTen_totient
    {length : Nat} (hlength : 0 < length) :
    (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card =
      Nat.totient 10 * 10 ^ (length - 1) := by
  rw [card_maynardCoprimeAmbientCarrier_powerTen hlength]
  have htotient : Nat.totient 10 = 4 := by decide
  rw [htotient]

theorem ten_mul_card_maynardCoprimeAmbientCarrier_powerTen
    {length : Nat} (hlength : 0 < length) :
    10 * (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card =
      Nat.totient 10 * (maynardAmbientCarrier ((10 ^ length : Nat) : Real)).card := by
  rw [card_maynardCoprimeAmbientCarrier_powerTen_totient hlength,
    card_maynardAmbientCarrier_natCast]
  have hpow : 10 ^ length = 10 * 10 ^ (length - 1) := by
    calc
      10 ^ length = 10 ^ (length - 1 + 1) := by
        rw [Nat.sub_add_cancel hlength]
      _ = 10 ^ (length - 1) * 10 := by rw [Nat.pow_succ]
      _ = 10 * 10 ^ (length - 1) := by ring
  rw [hpow]
  ring

theorem card_maynardCoprimeAmbientCarrier_powerTen_real_ratio
    {length : Nat} (hlength : 0 < length) :
    ((maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card : Real) =
      (Nat.totient 10 : Real) / 10 *
        ((maynardAmbientCarrier ((10 ^ length : Nat) : Real)).card : Real) := by
  have h := ten_mul_card_maynardCoprimeAmbientCarrier_powerTen hlength
  have hcast := congrArg (fun n : Nat => (n : Real)) h
  have htotient : Nat.totient 10 = 4 := by decide
  rw [htotient] at hcast ⊢
  norm_num at hcast ⊢
  linarith

/-- The ambient progression count at a decimal power of ten. -/
def ambientSieveProgressionCount (length q : Nat) : Nat :=
  ((maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).filter
    (fun n => q ∣ n)).card

/-- Signed ambient progression remainder, with the same normalization as the
source Type-I error. -/
def ambientSieveProgressionError (length q : Nat) : Real :=
  (ambientSieveProgressionCount length q : Real) -
    (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card /
      (q : Real)

private theorem ambientSieveProgressionCount_eq_coprime_count_ceil
    {length q : Nat} (hq : 0 < q) (hq10 : q.Coprime 10) :
    ambientSieveProgressionCount length q =
      Nat.count (fun n : Nat => n.Coprime 10)
        (Nat.ceil (((10 ^ length : Nat) : Real) / (q : Real))) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : PNat := ⟨q, hq⟩
  have hdil :
      sieveDilation (maynardCoprimeAmbientCarrier X) d =
      maynardCoprimeAmbientCarrier (X / (q : Real)) := by
    ext n
    rw [mem_sieveDilation, mem_maynardCoprimeAmbientCarrier,
      mem_maynardCoprimeAmbientCarrier]
    constructor
    · rintro ⟨hnX, hnTen⟩
      have hqReal : (0 : Real) < q := by exact_mod_cast hq
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hqReal]
        simpa [d, Nat.cast_mul, mul_comm] using hnX
      · exact (Nat.coprime_mul_iff_left.mp hnTen).1
    · rintro ⟨hnX, hnTen⟩
      have hqReal : (0 : Real) < q := by exact_mod_cast hq
      refine ⟨?_, Nat.coprime_mul_iff_left.mpr ⟨hnTen, hq10⟩⟩
      rw [lt_div_iff₀ hqReal] at hnX
      simpa [d, Nat.cast_mul, mul_comm] using hnX
  have hcardFilter :
      ambientSieveProgressionCount length q =
        (sieveDilation (maynardCoprimeAmbientCarrier X) d).card := by
    rw [ambientSieveProgressionCount]
    exact (card_sieveDilation_eq_card_filter_dvd
      (maynardCoprimeAmbientCarrier X) d).symm
  rw [hcardFilter, hdil, maynardCoprimeAmbientCarrier_eq_filter_range_ceil]
  exact (Nat.count_eq_card_filter_range
    (fun n : Nat => n.Coprime 10) _).symm

theorem ambientSieveProgressionError_abs_le
    {length q : Nat} (hlength : 0 < length) (hq : 0 < q)
    (hq10 : q.Coprime 10) :
    |ambientSieveProgressionError length q| <= 10 := by
  let N : Nat := 10 ^ length
  let X : Real := (N : Real)
  let M : Nat := Nat.ceil (X / (q : Real))
  have hcount := ambientSieveProgressionCount_eq_coprime_count_ceil
    (length := length) (q := q) hq hq10
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hMlower : (M : Real) - 1 < X / (q : Real) := by
    have hceil := Nat.ceil_lt_add_one (show 0 <= X / (q : Real) by positivity)
    linarith
  have hMupper : X / (q : Real) <= (M : Real) := by
    exact Nat.le_ceil _
  have hcardB :
      ((maynardCoprimeAmbientCarrier X).card : Real) =
        (2 / 5 : Real) * X := by
    rw [show X = (N : Real) by rfl, card_maynardCoprimeAmbientCarrier_powerTen
      (length := length) hlength]
    dsimp [N]
    have hpow : 10 ^ length = 10 * 10 ^ (length - 1) := by
      calc
        10 ^ length = 10 ^ (length - 1 + 1) := by
          rw [Nat.sub_add_cancel hlength]
        _ = 10 ^ (length - 1) * 10 := by rw [Nat.pow_succ]
        _ = 10 * 10 ^ (length - 1) := by ring
    norm_num [Nat.cast_mul]
    have hpowR : (10 ^ length : Real) =
        (10 : Real) * (10 ^ (length - 1) : Real) := by
      exact_mod_cast hpow
    rw [hpowR]
    ring
  rw [ambientSieveProgressionError, hcount, hcardB]
  have hcountErr := coprimeTen_count_real_error M
  have hMnonneg : 0 <= (M : Real) := by positivity
  have hscale :
      (2 / 5 : Real) * X / (q : Real) =
        (2 / 5 : Real) * (X / (q : Real)) := by ring
  rw [hscale]
  rw [abs_sub_comm]
  calc
    |(2 / 5 : Real) * (X / (q : Real)) -
          (Nat.count (fun n : Nat => n.Coprime 10) M : Real)| <=
        |(2 / 5 : Real) * (X / (q : Real)) -
          (2 / 5 : Real) * (M : Real)| +
          |(2 / 5 : Real) * (M : Real) -
            (Nat.count (fun n : Nat => n.Coprime 10) M : Real)| := by
      exact abs_sub_le _ _ _
    _ <= 10 := by
      have hfirst :
          |(2 / 5 : Real) * (M : Real) -
              (Nat.count (fun n : Nat => n.Coprime 10) M : Real)| <= 9 := by
        simpa [abs_sub_comm] using hcountErr
      have hsecond :
          |(2 / 5 : Real) * (X / (q : Real)) -
              (2 / 5 : Real) * (M : Real)| <= 1 := by
        have : |(M : Real) - X / (q : Real)| <= 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hdiff : |X / (q : Real) - (M : Real)| <= 1 := by
          simpa [abs_sub_comm] using this
        calc
          |(2 / 5 : Real) * (X / (q : Real)) -
                (2 / 5 : Real) * (M : Real)| =
              |(2 / 5 : Real)| * |X / (q : Real) - (M : Real)| := by
                rw [← mul_sub, abs_mul]
          _ = (2 / 5 : Real) * |X / (q : Real) - (M : Real)| := by
                rw [abs_of_nonneg (by norm_num : (0 : Real) <= 2 / 5)]
          _ <= 1 := by nlinarith
      linarith

/-- The reciprocal local-density function used by the ambient sieve. -/
def ambientReciprocalArithmeticFunction : ArithmeticFunction Real :=
  ⟨fun n => (n : Real)⁻¹, by simp⟩

@[simp] theorem ambientReciprocalArithmeticFunction_apply (n : Nat) :
    ambientReciprocalArithmeticFunction n = (n : Real)⁻¹ := rfl

theorem ambientReciprocalArithmeticFunction_isMultiplicative :
    ambientReciprocalArithmeticFunction.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [ambientReciprocalArithmeticFunction_apply, Nat.cast_mul]
    rw [mul_inv_rev, mul_comm]

/-- The reciprocal ambient sieve used in the proof of Eq. (7.8). -/
def ambientBoundingSieve (length : Nat) (d : PNat) (z : Real) : BoundingSieve where
  support := sieveDilation
    (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d
  prodPrimes := decimalSievePrimeProduct z
  prodPrimes_squarefree := squarefree_decimalSievePrimeProduct z
  weights := fun _ => 1
  weights_nonneg := by intro; norm_num
  totalMass :=
    (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card / (d : Real)
  nu := ambientReciprocalArithmeticFunction
  nu_mult := ambientReciprocalArithmeticFunction_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

@[simp] theorem ambientBoundingSieve_support
    (length : Nat) (d : PNat) (z : Real) :
    (ambientBoundingSieve length d z).support =
      sieveDilation
        (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d := rfl

@[simp] theorem ambientBoundingSieve_prodPrimes
    (length : Nat) (d : PNat) (z : Real) :
    (ambientBoundingSieve length d z).prodPrimes =
      decimalSievePrimeProduct z := rfl

@[simp] theorem ambientBoundingSieve_weights
    (length : Nat) (d : PNat) (z : Real) (n : Nat) :
    (ambientBoundingSieve length d z).weights n = 1 := rfl

@[simp] theorem ambientBoundingSieve_totalMass
    (length : Nat) (d : PNat) (z : Real) :
    (ambientBoundingSieve length d z).totalMass =
      (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card /
        (d : Real) := rfl

theorem ambientSieveDivisorCount_eq_progressionCount
    (length : Nat) (d e : PNat) :
    ((sieveDilation
        (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d).filter
      (fun n => (e : Nat) ∣ n)).card =
      ambientSieveProgressionCount length ((d : Nat) * (e : Nat)) := by
  let B := maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)
  calc
    ((sieveDilation B d).filter (fun n => (e : Nat) ∣ n)).card =
        (sieveDilation (sieveDilation B d) e).card := by
      exact (card_sieveDilation_eq_card_filter_dvd
        (sieveDilation B d) e).symm
    _ = (sieveDilation B (d * e)).card := by rw [sieveDilation_mul]
    _ = (B.filter (fun n => ((d : Nat) * (e : Nat)) ∣ n)).card := by
      exact card_sieveDilation_eq_card_filter_dvd B (d * e)
    _ = ambientSieveProgressionCount length ((d : Nat) * (e : Nat)) := by
      simp [B, ambientSieveProgressionCount]

theorem ambientBoundingSieve_multSum_eq
    (length : Nat) (d e : PNat) (z : Real) :
    (ambientBoundingSieve length d z).multSum e =
      (ambientSieveProgressionCount length ((d : Nat) * (e : Nat)) : Real) := by
  change (∑ n ∈ sieveDilation
      (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d,
      if (e : Nat) ∣ n then (1 : Real) else 0) = _
  rw [Finset.sum_boole]
  exact_mod_cast ambientSieveDivisorCount_eq_progressionCount length d e

theorem ambientBoundingSieve_rem_eq
    (length : Nat) (d e : PNat) (z : Real) :
    (ambientBoundingSieve length d z).rem e =
      ambientSieveProgressionError length ((d : Nat) * (e : Nat)) := by
  rw [BoundingSieve.rem, ambientBoundingSieve_multSum_eq,
    ambientSieveProgressionError]
  simp only [ambientBoundingSieve, ambientReciprocalArithmeticFunction_apply,
    Nat.cast_mul]
  have hd : (d : Real) ≠ 0 := by positivity
  have he : (e : Real) ≠ 0 := by positivity
  field_simp

theorem ambientBoundingSieve_siftedSum_eq_card
    (length : Nat) (d : PNat) {z : Real} (_hz : 5 <= z) :
    (ambientBoundingSieve length d z).siftedSum =
      ((strictSiftedCarrier
        (sieveDilation
          (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d) z).card : Real) := by
  let C := sieveDilation
    (maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)) d
  have hfilter :
      C.filter (fun n => (decimalSievePrimeProduct z).Coprime n) =
        strictSiftedCarrier C z := by
    ext n
    rw [Finset.mem_filter, mem_strictSiftedCarrier]
    constructor
    · rintro ⟨hnC, hnProduct⟩
      have hnFilter := mem_sieveDilation.mp hnC
      have hnTen : n.Coprime 10 := by
        have hprodTen := (Finset.mem_filter.mp hnFilter).2
        exact (Nat.coprime_mul_iff_left.mp hprodTen).1
      exact ⟨hnC,
        (coprime_decimalSievePrimeProduct_iff_strictRoughPredicate hnTen).mp
          hnProduct⟩
    · rintro ⟨hnC, hnRough⟩
      have hnFilter := mem_sieveDilation.mp hnC
      have hnTen : n.Coprime 10 := by
        have hprodTen := (Finset.mem_filter.mp hnFilter).2
        exact (Nat.coprime_mul_iff_left.mp hprodTen).1
      exact ⟨hnC,
        (coprime_decimalSievePrimeProduct_iff_strictRoughPredicate hnTen).mpr
          hnRough⟩
  change (∑ n ∈ C,
    if (decimalSievePrimeProduct z).Coprime n then 1 else 0) = _
  rw [Finset.sum_boole, hfilter]

end

end PrimesRestrictedDigits
