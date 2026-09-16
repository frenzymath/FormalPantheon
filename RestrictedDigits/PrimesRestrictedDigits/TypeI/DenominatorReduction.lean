import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Type I denominator reduction

This implements the two gcd reductions in the proof of Proposition 7.1 of
`MAYNARD-PRD-PUBLISHED`, p. 160. The source's cross-divisor uniqueness claim
is replaced by the explicit bound of four proved below.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A reduced Type I frequency is indexed by its decimal denominator part,
its divisor-of-`q` part, and its numerator. -/
abbrev TypeISplitIndex := (Nat × Nat) × Nat

private def typeIFirstQDenominator (b q : Nat) : Nat := q / b.gcd q

private def typeIFirstQNumerator (b q : Nat) : Nat := b / b.gcd q

/-- The two-stage gcd reduction of a source frequency `b/(d*q)`. -/
def typeIStagedSplitIndex (d q b : Nat) : TypeISplitIndex :=
  let firstNumerator := typeIFirstQNumerator b q
  let firstDenominator := typeIFirstQDenominator b q
  let decimalGcd := firstNumerator.gcd d
  ((d / decimalGcd, firstDenominator), firstNumerator / decimalGcd)

/-- The real rational frequency represented by a reduced Type I index. -/
noncomputable def typeISplitFractionValue (index : TypeISplitIndex) : Real :=
  (index.2 : Real) / ((index.1.1 * index.1.2 : Nat) : Real)

/-- Reduced frequencies with decimal part dividing `D` and modulus part
dividing `q`. -/
def typeISplitReducedCarrier (D q : Nat) : Finset TypeISplitIndex :=
  (((D.divisors.product q.divisors).product (Finset.range (D * q))).filter
    fun index =>
      index.2 < index.1.1 * index.1.2 ∧
        index.2.Coprime (index.1.1 * index.1.2))

/-- The reduced carrier after removing its modulus-one main block. -/
def typeINontrivialQSplitCarrier (D q : Nat) : Finset TypeISplitIndex :=
  (typeISplitReducedCarrier D q).filter fun index => 1 < index.1.2

private theorem typeIFirstQReduction {b d q : Nat}
    (hd : 0 < d) (hq : 0 < q) (hb : b < d * q) :
    let b' := typeIFirstQNumerator b q
    let q' := typeIFirstQDenominator b q
    0 < q' ∧ q' ∣ q ∧ b'.Coprime q' ∧ b' < d * q' ∧
      (b' : Real) / ((d * q' : Nat) : Real) =
        (b : Real) / ((d * q : Nat) : Real) ∧
      (q' = 1 ↔ q ∣ b) := by
  let g := b.gcd q
  let b' := typeIFirstQNumerator b q
  let q' := typeIFirstQDenominator b q
  have hg : 0 < g := Nat.gcd_pos_of_pos_right b hq
  have hgb : g ∣ b := Nat.gcd_dvd_left b q
  have hgq : g ∣ q := Nat.gcd_dvd_right b q
  have hbEq : b' * g = b := Nat.div_mul_cancel hgb
  have hqEq : q' * g = q := Nat.div_mul_cancel hgq
  have hq'Pos : 0 < q' := by
    exact Nat.div_pos (Nat.gcd_le_right b hq) hg
  have hq'Dvd : q' ∣ q := Nat.div_dvd_of_dvd hgq
  have hcop : b'.Coprime q' := Nat.coprime_div_gcd_div_gcd hg
  have hb'Lt : b' < d * q' := by
    apply (Nat.mul_lt_mul_right hg).mp
    rw [hbEq]
    calc
      b < d * q := hb
      _ = (d * q') * g := by rw [← hqEq, Nat.mul_assoc]
  have hvalue :
      (b' : Real) / ((d * q' : Nat) : Real) =
        (b : Real) / ((d * q : Nat) : Real) := by
    rw [← hbEq, ← hqEq]
    push_cast
    field_simp
  have hone : q' = 1 ↔ q ∣ b := by
    constructor
    · intro hq'One
      have hgqEq : g = q := Nat.eq_of_dvd_of_div_eq_one hgq hq'One
      exact Nat.gcd_eq_right_iff_dvd.mp hgqEq
    · intro hqb
      have hgEq : g = q := Nat.gcd_eq_right_iff_dvd.mpr hqb
      simp only [q', typeIFirstQDenominator, g, hgEq, Nat.div_self hq]
  exact ⟨hq'Pos, hq'Dvd, hcop, hb'Lt, hvalue, hone⟩

private theorem typeISecondDReduction {b d q : Nat}
    (hd : 0 < d) (hq : 0 < q) (hcoprime : b.Coprime q)
    (hb : b < d * q) :
    let g := b.gcd d
    let b' := b / g
    let d' := d / g
    d' ∣ d ∧ b'.Coprime (d' * q) ∧ b' < d' * q ∧
      (b' : Real) / ((d' * q : Nat) : Real) =
        (b : Real) / ((d * q : Nat) : Real) := by
  let g := b.gcd d
  let b' := b / g
  let d' := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right b hd
  have hgb : g ∣ b := Nat.gcd_dvd_left b d
  have hgd : g ∣ d := Nat.gcd_dvd_right b d
  have hbEq : b' * g = b := Nat.div_mul_cancel hgb
  have hdEq : d' * g = d := Nat.div_mul_cancel hgd
  have hd'Dvd : d' ∣ d := Nat.div_dvd_of_dvd hgd
  have hb'd' : b'.Coprime d' := Nat.coprime_div_gcd_div_gcd hg
  have hb'Dvd : b' ∣ b := Nat.div_dvd_of_dvd hgb
  have hb'q : b'.Coprime q := hcoprime.of_dvd_left hb'Dvd
  have hcop : b'.Coprime (d' * q) := hb'd'.mul_right hb'q
  have hb'Lt : b' < d' * q := by
    apply (Nat.mul_lt_mul_right hg).mp
    rw [hbEq]
    calc
      b < d * q := hb
      _ = (d' * q) * g := by rw [← hdEq]; ring
  have hvalue :
      (b' : Real) / ((d' * q : Nat) : Real) =
        (b : Real) / ((d * q : Nat) : Real) := by
    rw [← hbEq, ← hdEq]
    push_cast
    field_simp
  exact ⟨hd'Dvd, hcop, hb'Lt, hvalue⟩

private theorem typeIStagedSplitIndex_spec {D d q b : Nat}
    (hD : D ≠ 0) (hdD : d ∣ D) (hq : 0 < q)
    (_hcoprime : q.Coprime D) (hb : b < d * q) :
    typeIStagedSplitIndex d q b ∈ typeISplitReducedCarrier D q ∧
      typeISplitFractionValue (typeIStagedSplitIndex d q b) =
        (b : Real) / ((d * q : Nat) : Real) ∧
      ((typeIStagedSplitIndex d q b).1.2 = 1 ↔ q ∣ b) := by
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    simp only [zero_dvd_iff] at hdD
    exact hD hdD
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  let firstNumerator := typeIFirstQNumerator b q
  let firstDenominator := typeIFirstQDenominator b q
  let decimalGcd := firstNumerator.gcd d
  let decimalDenominator := d / decimalGcd
  let numerator := firstNumerator / decimalGcd
  rcases typeIFirstQReduction hd hq hb with
    ⟨hq'Pos, hq'Dvd, hfirstCoprime, hfirstLt, hfirstValue, hone⟩
  rcases typeISecondDReduction hd hq'Pos hfirstCoprime hfirstLt with
    ⟨hd'Dvd, hreducedCoprime, hreducedLt, hreducedValue⟩
  have hd'D : decimalDenominator ∣ D := hd'Dvd.trans hdD
  have hd'Le : decimalDenominator ≤ D := Nat.le_of_dvd hDpos hd'D
  have hq'Le : firstDenominator ≤ q := Nat.le_of_dvd hq hq'Dvd
  have hdenLe : decimalDenominator * firstDenominator ≤ D * q :=
    Nat.mul_le_mul hd'Le hq'Le
  have hmem : ((decimalDenominator, firstDenominator), numerator) ∈
      typeISplitReducedCarrier D q := by
    rw [typeISplitReducedCarrier, Finset.mem_filter]
    refine ⟨?_, hreducedLt, hreducedCoprime⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
      Finset.mem_range.mpr (hreducedLt.trans_le hdenLe)⟩
    · exact Nat.mem_divisors.mpr ⟨hd'D, hD⟩
    · exact Nat.mem_divisors.mpr ⟨hq'Dvd, hq.ne'⟩
  change ((decimalDenominator, firstDenominator), numerator) ∈
      typeISplitReducedCarrier D q ∧ _ ∧ _
  refine ⟨hmem, ?_, hone⟩
  rw [typeISplitFractionValue]
  exact hreducedValue.trans hfirstValue

private theorem typeIStagedSplitIndex_injectiveOn {d q : Nat}
    (hd : 0 < d) (hq : 0 < q) (hcoprime : d.Coprime q) :
    Set.InjOn (typeIStagedSplitIndex d q)
      (↑(Finset.range (d * q)) : Set Nat) := by
  intro left hleft right hright hequal
  have hleftValue := (typeIStagedSplitIndex_spec
    (D := d) hd.ne' (dvd_refl d) hq hcoprime.symm
      (Finset.mem_range.mp hleft)).2.1
  have hrightValue := (typeIStagedSplitIndex_spec
    (D := d) hd.ne' (dvd_refl d) hq hcoprime.symm
      (Finset.mem_range.mp hright)).2.1
  have hvalue := congrArg typeISplitFractionValue hequal
  rw [hleftValue, hrightValue] at hvalue
  have hm0 : (((d * q : Nat) : Real)) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hd hq).ne'
  field_simp [hm0] at hvalue
  exact_mod_cast hvalue

private theorem sum_typeIErrorFraction_le_nontrivialQSplitCarrier
    {D d q : Nat} (hD : D ≠ 0) (hdD : d ∣ D) (hq : 0 < q)
    (hcoprime : q.Coprime D) (f : Real → Real)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
      f ((b : Real) / ((d * q : Nat) : Real))) ≤
      ∑ index ∈ typeINontrivialQSplitCarrier D q,
        f (typeISplitFractionValue index) := by
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    simp only [zero_dvd_iff] at hdD
    exact hD hdD
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hqd : q.Coprime d :=
    Nat.Coprime.coprime_dvd_right hdD hcoprime
  let source := (Finset.range (d * q)).filter (fun b => ¬q ∣ b)
  let target := typeINontrivialQSplitCarrier D q
  let reduce := typeIStagedSplitIndex d q
  calc
    (∑ b ∈ source, f ((b : Real) / ((d * q : Nat) : Real))) =
        ∑ b ∈ source, f (typeISplitFractionValue (reduce b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbRange := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      rw [(typeIStagedSplitIndex_spec hD hdD hq hcoprime hbRange).2.1]
    _ = ∑ index ∈ source.image reduce,
          f (typeISplitFractionValue index) := by
      rw [Finset.sum_image]
      exact (typeIStagedSplitIndex_injectiveOn hd hq hqd.symm).mono
        (fun _ h => (Finset.mem_filter.mp h).1)
    _ ≤ ∑ index ∈ target, f (typeISplitFractionValue index) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro index hindex
        rcases Finset.mem_image.mp hindex with ⟨b, hb, rfl⟩
        rcases Finset.mem_filter.mp hb with ⟨hbRange, hbNotDvd⟩
        have hspec := typeIStagedSplitIndex_spec hD hdD hq hcoprime
          (Finset.mem_range.mp hbRange)
        have hfirst := typeIFirstQReduction hd hq
          (Finset.mem_range.mp hbRange)
        have hqPartPos : 0 < (typeIStagedSplitIndex d q b).1.2 := by
          change 0 < typeIFirstQDenominator b q
          exact hfirst.1
        have hqPartNe : (typeIStagedSplitIndex d q b).1.2 ≠ 1 := by
          intro hone
          exact hbNotDvd (hspec.2.2.mp hone)
        apply Finset.mem_filter.mpr
        have hqPartLt : 1 < (reduce b).1.2 := by
          change 1 < (typeIStagedSplitIndex d q b).1.2
          omega
        exact ⟨hspec.1, hqPartLt⟩
      · intro index hindex hnot
        exact hf _

/-- The nontrivial source frequencies map into the reduced carrier with
multiplicity at most the four divisors of ten. -/
theorem sum_divisors_ten_typeIErrorFraction_le
    {q : Nat} (hq : 0 < q) (hcoprime : q.Coprime 10)
    (f : Real → Real) (hf : ∀ x, 0 ≤ f x) :
    (∑ d ∈ (10 : Nat).divisors,
      ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
        f ((b : Real) / ((d * q : Nat) : Real))) ≤
      4 * ∑ index ∈ typeINontrivialQSplitCarrier 10 q,
        f (typeISplitFractionValue index) := by
  let target : Real := ∑ index ∈ typeINontrivialQSplitCarrier 10 q,
    f (typeISplitFractionValue index)
  have hcard : (10 : Nat).divisors.card = 4 := by decide
  calc
    (∑ d ∈ (10 : Nat).divisors,
        ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
          f ((b : Real) / ((d * q : Nat) : Real))) ≤
        ∑ _d ∈ (10 : Nat).divisors, target := by
      apply Finset.sum_le_sum
      intro d hd
      exact sum_typeIErrorFraction_le_nontrivialQSplitCarrier
        (D := 10) (d := d) (q := q) (by norm_num)
        (Nat.mem_divisors.mp hd).1 hq hcoprime f hf
    _ = 4 * target := by
      rw [Finset.sum_const, hcard]
      norm_num
    _ = 4 * ∑ index ∈ typeINontrivialQSplitCarrier 10 q,
          f (typeISplitFractionValue index) := rfl

end PrimesRestrictedDigits
