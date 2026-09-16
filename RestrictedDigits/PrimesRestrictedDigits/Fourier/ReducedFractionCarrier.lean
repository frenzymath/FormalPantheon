import PrimesRestrictedDigits.Fourier.RationalCircleSpacing
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Interval

/-!
# Finite reduced-fraction carriers

These carriers encode the two Farey sums in `MAYNARD-PRD-PUBLISHED`, Lemma 10.5, with
denominator first and numerator second.
-/

namespace PrimesRestrictedDigits

/-- Reduced fractions `a/q` with `1 <= q <= N` and `0 < a < q`. -/
def reducedFractionCarrier (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.Icc 1 N).product (Finset.range N)).filter fun pair =>
    0 < pair.2 ∧ pair.2 < pair.1 ∧ pair.2.Coprime pair.1

theorem mem_reducedFractionCarrier_iff {N : Nat} {pair : Nat × Nat} :
    pair ∈ reducedFractionCarrier N ↔
      1 <= pair.1 ∧ pair.1 <= N ∧ 0 < pair.2 ∧ pair.2 < pair.1 ∧
        pair.2.Coprime pair.1 := by
  constructor
  · intro hpair
    rcases Finset.mem_filter.mp hpair with ⟨hproduct, hconditions⟩
    rcases Finset.mem_product.mp hproduct with ⟨hdenominator, hnumerator⟩
    rw [Finset.mem_Icc] at hdenominator
    exact ⟨hdenominator.1, hdenominator.2, hconditions.1,
      hconditions.2.1, hconditions.2.2⟩
  · rintro ⟨hq1, hqN, ha0, haq, hcoprime⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hq1, hqN⟩,
        Finset.mem_range.mpr (haq.trans_le hqN)⟩
    · exact ⟨ha0, haq, hcoprime⟩

/-- The canonical rational represented by a carrier pair. -/
def reducedFractionRat (pair : Nat × Nat) : Rat :=
  (pair.2 : Rat) / (pair.1 : Rat)

/-- The real frequency represented by a carrier pair. -/
noncomputable def reducedFractionValue (pair : Nat × Nat) : Real :=
  (pair.2 : Real) / (pair.1 : Real)

theorem ratCast_reducedFractionRat (pair : Nat × Nat) :
    (reducedFractionRat pair : Real) = reducedFractionValue pair := by
  norm_num [reducedFractionRat, reducedFractionValue]

private theorem intNatAbs_coprime_of_natCoprime
    {a q : Nat} (hcoprime : a.Coprime q) :
    (a : Int).natAbs.Coprime (q : Int).natAbs := by
  simpa using hcoprime

theorem reducedFractionRat_den_eq {N : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ reducedFractionCarrier N) :
    (reducedFractionRat pair).den = pair.1 := by
  have hmem := mem_reducedFractionCarrier_iff.mp hpair
  have hq : 0 < pair.1 := lt_of_lt_of_le Nat.zero_lt_one hmem.1
  have hden := Rat.den_div_eq_of_coprime
    (a := (pair.2 : Int)) (b := (pair.1 : Int))
    (by exact_mod_cast hq : (0 : Int) < (pair.1 : Int))
    (intNatAbs_coprime_of_natCoprime hmem.2.2.2.2)
  have hcast : reducedFractionRat pair =
      ((pair.2 : Int) : Rat) / ((pair.1 : Int) : Rat) := by
    norm_num [reducedFractionRat]
  calc
    (reducedFractionRat pair).den =
        ((((pair.2 : Int) : Rat) / ((pair.1 : Int) : Rat))).den :=
      congrArg Rat.den hcast
    _ = pair.1 := by exact_mod_cast hden

theorem reducedFractionRat_pos {N : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ reducedFractionCarrier N) :
    0 < reducedFractionRat pair := by
  have hmem := mem_reducedFractionCarrier_iff.mp hpair
  change (0 : Rat) < (pair.2 : Rat) / (pair.1 : Rat)
  exact div_pos (by exact_mod_cast hmem.2.2.1)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmem.1))

theorem reducedFractionRat_lt_one {N : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ reducedFractionCarrier N) :
    reducedFractionRat pair < 1 := by
  have hmem := mem_reducedFractionCarrier_iff.mp hpair
  have hq : (0 : Rat) < pair.1 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmem.1)
  change (pair.2 : Rat) / (pair.1 : Rat) < 1
  rw [div_lt_one hq]
  exact_mod_cast hmem.2.2.2.1

theorem reducedFractionRat_injectiveOn (N : Nat) :
    Set.InjOn reducedFractionRat (↑(reducedFractionCarrier N) : Set (Nat × Nat)) := by
  intro left hleft right hright hequal
  have hleftMem := mem_reducedFractionCarrier_iff.mp hleft
  have hrightMem := mem_reducedFractionCarrier_iff.mp hright
  have hleftDen : (0 : Int) < (left.1 : Int) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hleftMem.1)
  have hrightDen : (0 : Int) < (right.1 : Int) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hrightMem.1)
  have hunique := Rat.div_int_inj hleftDen hrightDen
    (intNatAbs_coprime_of_natCoprime hleftMem.2.2.2.2)
    (intNatAbs_coprime_of_natCoprime hrightMem.2.2.2.2)
    (by simpa [reducedFractionRat] using hequal)
  apply Prod.ext
  · exact_mod_cast hunique.2
  · exact_mod_cast hunique.1

theorem one_div_sq_le_dist_reducedFractionValue
    {N : Nat} {left right : Nat × Nat} {Q : Real}
    (_hQ : 0 <= Q) (hleft : left ∈ reducedFractionCarrier N)
    (hright : right ∈ reducedFractionCarrier N)
    (hNQ : (N : Real) <= Q) (hne : left ≠ right) :
    1 / Q ^ 2 <=
      dist ((reducedFractionValue left : Real) : UnitAddCircle)
        ((reducedFractionValue right : Real) : UnitAddCircle) := by
  have hratNe : reducedFractionRat left ≠ reducedFractionRat right := by
    intro hrat
    exact hne (reducedFractionRat_injectiveOn N hleft hright hrat)
  have hcircleNe := unitAddCircle_rat_ne_of_mem_Ico
    (reducedFractionRat_pos hleft).le (reducedFractionRat_lt_one hleft)
    (reducedFractionRat_pos hright).le (reducedFractionRat_lt_one hright) hratNe
  have hleftDen : ((reducedFractionRat left).den : Real) <= Q := by
    rw [reducedFractionRat_den_eq hleft]
    exact (by exact_mod_cast
      (mem_reducedFractionCarrier_iff.mp hleft).2.1 : (left.1 : Real) <= N).trans hNQ
  have hrightDen : ((reducedFractionRat right).den : Real) <= Q := by
    rw [reducedFractionRat_den_eq hright]
    exact (by exact_mod_cast
      (mem_reducedFractionCarrier_iff.mp hright).2.1 : (right.1 : Real) <= N).trans hNQ
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity : (0 : Real) < 1)
    ((by exact_mod_cast (mem_reducedFractionCarrier_iff.mp hleft).1 :
      (1 : Real) <= left.1).trans
        ((by exact_mod_cast
          (mem_reducedFractionCarrier_iff.mp hleft).2.1 : (left.1 : Real) <= N).trans hNQ))
  simpa only [ratCast_reducedFractionRat] using
    one_div_sq_le_dist_rat_of_den_le hQ0 hleftDen hrightDen hcircleNe

/-- The subcarrier whose denominators are divisible by `d`. -/
def divisibleReducedFractionCarrier (N d : Nat) : Finset (Nat × Nat) :=
  (reducedFractionCarrier N).filter fun pair => d ∣ pair.1

theorem mem_divisibleReducedFractionCarrier_iff
    {N d : Nat} {pair : Nat × Nat} :
    pair ∈ divisibleReducedFractionCarrier N d ↔
      pair ∈ reducedFractionCarrier N ∧ d ∣ pair.1 := by
  simp [divisibleReducedFractionCarrier]

theorem natCast_div_sq_le_dist_divisibleReducedFractionValue
    {N d : Nat} {left right : Nat × Nat} {Q : Real}
    (hd : 0 < d) (hQ : 0 < Q)
    (hleft : left ∈ divisibleReducedFractionCarrier N d)
    (hright : right ∈ divisibleReducedFractionCarrier N d)
    (hNQ : (N : Real) <= Q) (hne : left ≠ right) :
    (d : Real) / Q ^ 2 <=
      dist ((reducedFractionValue left : Real) : UnitAddCircle)
        ((reducedFractionValue right : Real) : UnitAddCircle) := by
  have hleft' := mem_divisibleReducedFractionCarrier_iff.mp hleft
  have hright' := mem_divisibleReducedFractionCarrier_iff.mp hright
  have hratNe : reducedFractionRat left ≠ reducedFractionRat right := by
    intro hrat
    exact hne (reducedFractionRat_injectiveOn N hleft'.1 hright'.1 hrat)
  have hcircleNe := unitAddCircle_rat_ne_of_mem_Ico
    (reducedFractionRat_pos hleft'.1).le (reducedFractionRat_lt_one hleft'.1)
    (reducedFractionRat_pos hright'.1).le (reducedFractionRat_lt_one hright'.1) hratNe
  have hleftDen : ((reducedFractionRat left).den : Real) <= Q := by
    rw [reducedFractionRat_den_eq hleft'.1]
    exact (by exact_mod_cast
      (mem_reducedFractionCarrier_iff.mp hleft'.1).2.1 : (left.1 : Real) <= N).trans hNQ
  have hrightDen : ((reducedFractionRat right).den : Real) <= Q := by
    rw [reducedFractionRat_den_eq hright'.1]
    exact (by exact_mod_cast
      (mem_reducedFractionCarrier_iff.mp hright'.1).2.1 : (right.1 : Real) <= N).trans hNQ
  have hdLeft : d ∣ (reducedFractionRat left).den := by
    rw [reducedFractionRat_den_eq hleft'.1]
    exact hleft'.2
  have hdRight : d ∣ (reducedFractionRat right).den := by
    rw [reducedFractionRat_den_eq hright'.1]
    exact hright'.2
  simpa only [ratCast_reducedFractionRat] using
    natCast_div_sq_le_dist_rat_of_den_le hd hQ hdLeft hdRight
      hleftDen hrightDen hcircleNe

end PrimesRestrictedDigits
