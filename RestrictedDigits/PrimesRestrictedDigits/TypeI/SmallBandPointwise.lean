import PrimesRestrictedDigits.TypeI.LargeSieveBandScalars
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pointwise estimate on one small Type I band

This specializes published Lemma 8.2 to the existing real-capped decimal fibers and retains
the exact harmonic weight.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The explicit common decay factor on a Type I band with upper scale `R`. -/
def typeISmallBandDecay (length : Nat) (R : Real) : Real :=
  Real.exp (-(1 / 100000000 : Real) *
    (Real.log (((10 ^ length : Nat) : Real)) / Real.log (10 * R)))

/-- An active scale contains a reduced denominator greater than one. -/
theorem two_le_typeIDecadeScale_of_mem
    {Q R : Real} (hR : R ∈ typeIDecadeScalesBelow Q) : (2 : Real) ≤ R := by
  classical
  rcases Finset.mem_image.mp hR with ⟨q, hqCarrier, hqScale⟩
  have hqFiber : q ∈ typeIDecadeFiber Q R :=
    Finset.mem_filter.mpr ⟨hqCarrier, hqScale⟩
  have hqData := typeIDecadeFiber_data hqFiber
  have hqTwo : (2 : Real) ≤ q := by
    exact_mod_cast (show 2 ≤ q by omega)
  exact hqTwo.trans hqData.2.2.2

/-- The number of reduced denominators in a real-capped fiber is at most its
real upper endpoint. -/
theorem card_typeIDecadeFiber_cast_le
    {Q R : Real} (hR : R ∈ typeIDecadeScalesBelow Q) :
    ((typeIDecadeFiber Q R).card : Real) ≤ R := by
  have hsubset : typeIDecadeFiber Q R ⊆ Finset.Icc 1 (Nat.floor R) := by
    intro q hq
    have hdata := typeIDecadeFiber_data hq
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hdata.2.2.2⟩
  have hcardNat : (typeIDecadeFiber Q R).card ≤ Nat.floor R := by
    calc
      (typeIDecadeFiber Q R).card ≤ (Finset.Icc 1 (Nat.floor R)).card :=
        Finset.card_le_card hsubset
      _ = Nat.floor R := by simp [Nat.card_Icc]
  have hcardReal : ((typeIDecadeFiber Q R).card : Real) ≤ Nat.floor R := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (Nat.floor_le (typeIDecadeScale_pos_of_mem hR).le)

/-- The explicit Lemma 8.2 estimate, uniform on one real-capped fiber. -/
theorem typeILInfEstimate_on_decadeFiber
    (digit : Fin 10) {length d q b : Nat} {Q R : Real}
    (hd : d ∈ Nat.divisors 10) (hq : q ∈ typeIDecadeFiber Q R)
    (hb : b.Coprime (d * q))
    (hden : ((d * q : Nat) : Real) <
      (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real))) :
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((b : Real) / ((d * q : Nat) : Real)) ≤
      3 * typeISmallBandDecay length R := by
  rcases typeIDecadeFiber_data hq with ⟨hqOne, hqTen, _, hqR⟩
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdLe : d ≤ 10 := Nat.divisor_le hd
  have heta : |(0 : Real)| <
      (((10 ^ length : Nat) : Real) ^ (-2 / 3 : Real)) / 2 := by
    rw [abs_zero]
    positivity
  have hsource := typeILInfEstimate digit
    (length := length) (q := d * q) (q1 := q) (q2 := d)
    (a := (b : Int)) (eta := 0) (Nat.mul_comm d q) hdPos hqOne hqTen
    (by simpa using hb) hden heta
  have htotalOneNat : 1 < d * q := by
    have hqLe : q ≤ d * q := by
      have h := Nat.mul_le_mul_right q (Nat.succ_le_iff.mp hdPos)
      norm_num at h
      exact h
    omega
  have htotalOne : (1 : Real) < ((d * q : Nat) : Real) := by
    exact_mod_cast htotalOneNat
  have hdLeReal : (d : Real) ≤ 10 := by exact_mod_cast hdLe
  have htotalLe : ((d * q : Nat) : Real) ≤ 10 * R := by
    push_cast
    exact mul_le_mul hdLeReal hqR (by positivity) (by norm_num)
  have hlogTotalPos : 0 < Real.log ((d * q : Nat) : Real) :=
    Real.log_pos htotalOne
  have hlogTenRPos : 0 < Real.log (10 * R) :=
    Real.log_pos (htotalOne.trans_le htotalLe)
  have hlogLe : Real.log ((d * q : Nat) : Real) ≤ Real.log (10 * R) :=
    Real.log_le_log (zero_lt_one.trans htotalOne) htotalLe
  have hXOne : (1 : Real) ≤ ((10 ^ length : Nat) : Real) := by
    exact_mod_cast (Nat.one_le_pow' length 9)
  have hlogXNonneg : 0 ≤ Real.log (((10 ^ length : Nat) : Real)) :=
    Real.log_nonneg hXOne
  have hquotient :
      Real.log (((10 ^ length : Nat) : Real)) / Real.log (10 * R) ≤
        Real.log (((10 ^ length : Nat) : Real)) /
          Real.log ((d * q : Nat) : Real) :=
    div_le_div_of_nonneg_left hlogXNonneg hlogTotalPos hlogLe
  have hnegative :
      -(1 / 100000000 : Real) *
          (Real.log (((10 ^ length : Nat) : Real)) /
            Real.log ((d * q : Nat) : Real)) ≤
        -(1 / 100000000 : Real) *
          (Real.log (((10 ^ length : Nat) : Real)) / Real.log (10 * R)) :=
    mul_le_mul_of_nonpos_left hquotient (by norm_num)
  simpa only [Int.cast_natCast, add_zero, typeISmallBandDecay] using
    hsource.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hnegative) (by norm_num))

/-- After division by the harmonic denominator, the numerator count cancels
the factor `q`; only the fixed divisor `d ≤ 10` remains. -/
theorem typeIReducedFrequencyMass_div_le_on_decadeFiber
    (digit : Fin 10) {length d q : Nat} {Q R : Real}
    (hd : d ∈ Nat.divisors 10) (hq : q ∈ typeIDecadeFiber Q R)
    (hden : ((d * q : Nat) : Real) <
      (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real))) :
    typeIReducedFrequencyMass digit length d q / (q : Real) ≤
      30 * typeISmallBandDecay length R := by
  let E := typeISmallBandDecay length R
  have hE : 0 ≤ E := by
    dsimp [E, typeISmallBandDecay]
    positivity
  have hsum : typeIReducedFrequencyMass digit length d q ≤
      ((Finset.range (d * q)).filter
        (fun b => b.Coprime (d * q))).card • (3 * E) := by
    apply Finset.sum_le_card_nsmul
    intro b hb
    exact typeILInfEstimate_on_decadeFiber digit hd hq
      (Finset.mem_filter.mp hb).2 hden
  have hcard : ((Finset.range (d * q)).filter
      (fun b => b.Coprime (d * q))).card ≤ d * q :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hdLe : d ≤ 10 := Nat.divisor_le hd
  have hqPos : (0 : Real) < q := by
    have hqPosNat : 0 < q := by
      have hqOne := (typeIDecadeFiber_data hq).1
      omega
    exact_mod_cast hqPosNat
  have hcardReal :
      (((Finset.range (d * q)).filter
        (fun b => b.Coprime (d * q))).card : Real) ≤ (d * q : Nat) := by
    exact_mod_cast hcard
  have hproductNat : d * q ≤ 10 * q := Nat.mul_le_mul_right q hdLe
  have hproductReal : ((d * q : Nat) : Real) ≤ (10 * q : Nat) := by
    exact_mod_cast hproductNat
  apply (div_le_iff₀ hqPos).2
  calc
    typeIReducedFrequencyMass digit length d q ≤
        ((Finset.range (d * q)).filter
          (fun b => b.Coprime (d * q))).card • (3 * E) := hsum
    _ = (((Finset.range (d * q)).filter
          (fun b => b.Coprime (d * q))).card : Real) * (3 * E) := by simp
    _ ≤ ((d * q : Nat) : Real) * (3 * E) :=
      mul_le_mul_of_nonneg_right hcardReal (by positivity)
    _ ≤ ((10 * q : Nat) : Real) * (3 * E) :=
      mul_le_mul_of_nonneg_right hproductReal (by positivity)
    _ = (30 * E) * (q : Real) := by
      push_cast
      ring

/-- The exact weighted contribution of one active fiber is controlled by its
real upper endpoint, including a nonintegral final capped band. -/
theorem sum_typeIDecadeFiber_div_le_lInf
    (digit : Fin 10) (length d : Nat) {Q R : Real}
    (hd : d ∈ Nat.divisors 10) (hR : R ∈ typeIDecadeScalesBelow Q)
    (hden : ∀ q ∈ typeIDecadeFiber Q R,
      ((d * q : Nat) : Real) <
        (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real))) :
    (∑ q ∈ typeIDecadeFiber Q R,
      typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
      30 * R * typeISmallBandDecay length R := by
  let E := typeISmallBandDecay length R
  have hE : 0 ≤ E := by
    dsimp [E, typeISmallBandDecay]
    positivity
  have hsum : (∑ q ∈ typeIDecadeFiber Q R,
      typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
      (typeIDecadeFiber Q R).card • (30 * E) := by
    apply Finset.sum_le_card_nsmul
    intro q hq
    exact typeIReducedFrequencyMass_div_le_on_decadeFiber digit hd hq
      (hden q hq)
  calc
    (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        (typeIDecadeFiber Q R).card • (30 * E) := hsum
    _ = ((typeIDecadeFiber Q R).card : Real) * (30 * E) := by simp
    _ ≤ R * (30 * E) :=
      mul_le_mul_of_nonneg_right (card_typeIDecadeFiber_cast_le hR)
        (by positivity)
    _ = 30 * R * typeISmallBandDecay length R := by
      dsimp [E]
      ring

end

end PrimesRestrictedDigits
