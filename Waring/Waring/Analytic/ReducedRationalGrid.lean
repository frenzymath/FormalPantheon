import Waring.Analytic.DiophantineMinimumSum

/-!
# Reduction to a primitive rational grid

This file cancels the gcd of a rational frequency and its modulus before
applying the complete-grid estimate in Chen's Lemma 9 [CHEN1964-EN, p. 1560,
equations (22)-(23)].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The common factor cancelled from a rational-grid frequency and modulus. -/
def rationalGridGcd (c q : Nat) : Nat := Nat.gcd c q

/-- The modulus remaining after rational-grid gcd cancellation. -/
def reducedGridDenominator (c q : Nat) : Nat := q / rationalGridGcd c q

/-- The frequency coefficient remaining after rational-grid gcd cancellation. -/
def reducedGridCoefficient (c q : Nat) : Nat := c / rationalGridGcd c q

/-- The rational-grid gcd is positive when the modulus is positive. -/
theorem rationalGridGcd_pos (c q : Nat) [NeZero q] :
    0 < rationalGridGcd c q := by
  exact Nat.gcd_pos_of_pos_right c (NeZero.pos q)

/-- The reduced denominator is positive when the original modulus is positive. -/
theorem reducedGridDenominator_pos (c q : Nat) [NeZero q] :
    0 < reducedGridDenominator c q := by
  apply Nat.div_pos
  · exact Nat.gcd_le_right c (NeZero.pos q)
  · exact rationalGridGcd_pos c q

/-- A positive modulus gives a positive reduced rational-grid denominator. -/
instance instNeZeroReducedGridDenominator (c q : Nat) [NeZero q] :
    NeZero (reducedGridDenominator c q) :=
  ⟨(reducedGridDenominator_pos c q).ne'⟩

/-- Cancelling and then restoring the common factor recovers the modulus. -/
theorem rationalGridGcd_mul_reducedGridDenominator (c q : Nat) :
    rationalGridGcd c q * reducedGridDenominator c q = q := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right c q)

/-- Cancelling and then restoring the common factor recovers the coefficient. -/
theorem rationalGridGcd_mul_reducedGridCoefficient (c q : Nat) :
    rationalGridGcd c q * reducedGridCoefficient c q = c := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left c q)

/-- The coefficient and denominator obtained by gcd cancellation are coprime. -/
theorem reducedGridCoefficient_coprime (c q : Nat) [NeZero q] :
    (reducedGridCoefficient c q).Coprime (reducedGridDenominator c q) := by
  exact Nat.coprime_div_gcd_div_gcd (rationalGridGcd_pos c q)

/-- The reduced coefficient is a unit modulo the reduced denominator. -/
theorem reducedGridCoefficient_isUnit (c q : Nat) [NeZero q] :
    IsUnit (reducedGridCoefficient c q : ZMod (reducedGridDenominator c q)) := by
  exact (ZMod.isUnit_iff_coprime _ _).2 (reducedGridCoefficient_coprime c q)

/-- A reduced denominator never exceeds its original positive modulus. -/
theorem reducedGridDenominator_le (c q : Nat) :
    reducedGridDenominator c q ≤ q := by
  exact Nat.div_le_self q (rationalGridGcd c q)

/-- If `a` is coprime to `q`, multiplying another coefficient by `a` does not
change its gcd with `q`. -/
theorem rationalGridGcd_mul_eq_of_coprime {a q : Nat} (k : Nat)
    (ha : a.Coprime q) :
    rationalGridGcd (k * a) q = Nat.gcd k q := by
  exact ha.gcd_mul_right_cancel k

/-- For a primitive residue `a`, Chen's cancelled factor is exactly
`gcd(120,q)`. -/
theorem rationalGridGcd_oneHundredTwenty_mul_val {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    rationalGridGcd (120 * a.val) q = Nat.gcd 120 q := by
  have haCoprime : a.val.Coprime q := by
    apply (ZMod.isUnit_iff_coprime _ _).1
    simpa using ha
  exact rationalGridGcd_mul_eq_of_coprime 120 haCoprime

/-- Chen's cancelled factor is at most `120` for a primitive residue. -/
theorem rationalGridGcd_oneHundredTwenty_mul_val_le {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    rationalGridGcd (120 * a.val) q ≤ 120 := by
  rw [rationalGridGcd_oneHundredTwenty_mul_val a ha]
  exact Nat.gcd_le_left q (by norm_num)

/-- Chen's reduced denominator is at least `q / 120`. -/
theorem div_oneHundredTwenty_le_reducedGridDenominator {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    q / 120 ≤ reducedGridDenominator (120 * a.val) q := by
  exact Nat.div_le_div_left
    (rationalGridGcd_oneHundredTwenty_mul_val_le a ha)
    (rationalGridGcd_pos (120 * a.val) q)

/-- Scaling both an integer residue and its positive modulus scales the least
absolute representative by the same positive factor. -/
theorem valMinAbs_scaled_modulus (d q : Nat) [NeZero d] [NeZero q] (x : Int) :
    (((d : Int) * x : Int) : ZMod (d * q)).valMinAbs =
      (d : Int) * ((x : ZMod q).valMinAbs) := by
  apply (ZMod.valMinAbs_spec _ _).2
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ (d * q)).2
    have hmod : x ≡ (x : ZMod q).valMinAbs [ZMOD (q : Int)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ q).1
      simp
    simpa only [Int.natCast_mul] using hmod.mul_left'
  · have hr := (x : ZMod q).valMinAbs_mem_Ioc
    have hd : (0 : Int) < d := by exact_mod_cast NeZero.pos d
    constructor
    · have h := mul_lt_mul_of_pos_left hr.1 hd
      push_cast at h ⊢
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hr.2 hd.le
      push_cast at h ⊢
      nlinarith

/-- Scaling both residue and modulus scales its unsigned least-residue distance. -/
theorem natAbs_valMinAbs_scaled_modulus (d q : Nat) [NeZero d] [NeZero q]
    (x : Int) :
    (((d : Int) * x : Int) : ZMod (d * q)).valMinAbs.natAbs =
      d * (x : ZMod q).valMinAbs.natAbs := by
  rw [valMinAbs_scaled_modulus, Int.natAbs_mul, Int.natAbs_natCast]

/-- Changing a positive modulus along an equality preserves the weight of the
same integer representative. -/
theorem diophantineMinWeight_modulus_congr {q r : Nat} [NeZero q] [NeZero r]
    (h : q = r) (P : Nat) (x : Int) :
    diophantineMinWeight q P (x : ZMod q) =
      diophantineMinWeight r P (x : ZMod r) := by
  subst r
  rfl

/-- Scaling a residue and its modulus by the same positive factor preserves the
zero-safe reciprocal-distance weight exactly. -/
theorem diophantineMinWeight_scaled_modulus (d q P : Nat) [NeZero d] [NeZero q]
    (x : Int) :
    diophantineMinWeight (d * q) P
        (((d : Int) * x : Int) : ZMod (d * q)) =
      diophantineMinWeight q P (x : ZMod q) := by
  let leftResidue : ZMod (d * q) := ((d : Int) * x : Int)
  let rightResidue : ZMod q := x
  have hval : leftResidue.valMinAbs =
      (d : Int) * rightResidue.valMinAbs := by
    exact valMinAbs_scaled_modulus d q x
  have hzero : leftResidue = 0 ↔ rightResidue = 0 := by
    rw [← ZMod.valMinAbs_eq_zero, hval, mul_eq_zero]
    simp [NeZero.ne d]
  by_cases hr : rightResidue = 0
  · simp [diophantineMinWeight, leftResidue, rightResidue, hr, hzero.mpr hr]
  have hl : leftResidue ≠ 0 := fun h ↦ hr (hzero.mp h)
  rw [diophantineMinWeight, if_neg hl, diophantineMinWeight, if_neg hr]
  congr 1
  simp only [leastResidueWeight, natAbs_valMinAbs_scaled_modulus]
  push_cast
  have hd : (d : Real) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdistance : (((x : ZMod q).valMinAbs.natAbs : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Int.natAbs_ne_zero.mpr
      ((ZMod.valMinAbs_eq_zero (x : ZMod q)).not.mpr hr))
  field_simp

/-- Cancelling the gcd of a natural coefficient and a positive modulus
preserves every integer-frequency weight. -/
theorem diophantineMinWeight_gcd_reduce (c q P : Nat) [NeZero q] (m : Int) :
    diophantineMinWeight q P (((c : Int) * m : Int) : ZMod q) =
      diophantineMinWeight (reducedGridDenominator c q) P
        (((reducedGridCoefficient c q : Nat) : Int) * m : Int) := by
  let d := rationalGridGcd c q
  let Q := reducedGridDenominator c q
  let C := reducedGridCoefficient c q
  have hd : 0 < d := rationalGridGcd_pos c q
  letI : NeZero d := ⟨hd.ne'⟩
  have hq : d * Q = q := rationalGridGcd_mul_reducedGridDenominator c q
  have hc : d * C = c := rationalGridGcd_mul_reducedGridCoefficient c q
  have hscale := diophantineMinWeight_scaled_modulus d Q P ((C : Int) * m)
  have hcInt : (c : Int) * m = (d : Int) * ((C : Int) * m) := by
    rw [← hc]
    push_cast
    ring
  calc
    diophantineMinWeight q P (((c : Int) * m : Int) : ZMod q) =
        diophantineMinWeight (d * Q) P
          (((c : Int) * m : Int) : ZMod (d * Q)) :=
      diophantineMinWeight_modulus_congr hq.symm P ((c : Int) * m)
    _ = diophantineMinWeight (d * Q) P
          (((d : Int) * ((C : Int) * m) : Int) : ZMod (d * Q)) := by
      rw [hcInt]
    _ = diophantineMinWeight Q P (((C : Int) * m : Int) : ZMod Q) := hscale

/-- Gcd cancellation preserves the negative natural frequencies used in
Chen's product sum. -/
theorem diophantineMinWeight_neg_nat_mul_gcd_reduce
    (c q P m : Nat) [NeZero q] :
    diophantineMinWeight q P (-((c * m : Nat) : ZMod q)) =
      diophantineMinWeight (reducedGridDenominator c q) P
        (-((reducedGridCoefficient c q * m : Nat) :
          ZMod (reducedGridDenominator c q))) := by
  simpa only [Int.mul_neg, Int.cast_neg, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul] using
      (diophantineMinWeight_gcd_reduce c q P (-(m : Int)))

/-- Gcd cancellation preserves the complete initial-range sum pointwise. -/
theorem sum_range_diophantineMinWeight_neg_mul_gcd_reduce
    (c q P X : Nat) [NeZero q] :
    (∑ m ∈ Finset.range X,
        diophantineMinWeight q P (-((c * m : Nat) : ZMod q))) =
      ∑ m ∈ Finset.range X,
        diophantineMinWeight (reducedGridDenominator c q) P
          (-((reducedGridCoefficient c q * m : Nat) :
            ZMod (reducedGridDenominator c q))) := by
  apply Finset.sum_congr rfl
  intro m _
  exact diophantineMinWeight_neg_nat_mul_gcd_reduce c q P m

/-- An affine unit permutation and repetition over an initial interval cost at
most the maximal residue-fiber cardinality times one complete residue sum. -/
theorem sum_range_diophantineMinWeight_affine_le
    (q P X : Nat) [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    (∑ i ∈ Finset.range X,
        diophantineMinWeight q P (a * (i : ZMod q) + b)) ≤
      ((X / q + 1 : Nat) : Real) *
        ((P : Real) + q * Real.log q) := by
  let residue : Nat → ZMod q := fun i ↦ i
  have hmaps : ∀ i ∈ Finset.range X,
      residue i ∈ (Finset.univ : Finset (ZMod q)) := by simp
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps
    (fun h ↦ diophantineMinWeight q P (a * h + b))]
  have hsum :
      (∑ h : ZMod q,
          ∑ _i ∈ Finset.range X with residue _i = h,
            diophantineMinWeight q P (a * h + b)) ≤
        ∑ h : ZMod q, ((X / q + 1 : Nat) : Real) *
          diophantineMinWeight q P (a * h + b) := by
    apply Finset.sum_le_sum
    intro h _
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast card_range_zmod_fiber_le q X h
    · exact diophantineMinWeight_nonneg q P (a * h + b)
  calc
    (∑ h : ZMod q,
        ∑ _i ∈ Finset.range X with residue _i = h,
          diophantineMinWeight q P (a * h + b)) ≤
        ∑ h : ZMod q, ((X / q + 1 : Nat) : Real) *
          diophantineMinWeight q P (a * h + b) := hsum
    _ = ((X / q + 1 : Nat) : Real) *
          ∑ h : ZMod q, diophantineMinWeight q P (a * h + b) := by
      rw [Finset.mul_sum]
    _ = ((X / q + 1 : Nat) : Real) *
          ∑ h : ZMod q, diophantineMinWeight q P h := by
      obtain ⟨u, rfl⟩ := ha
      congr 1
      let e : ZMod q ≃ ZMod q := u.mulLeft.trans (Equiv.addRight b)
      simpa only [e, Equiv.trans_apply, Units.mulLeft_apply,
        Equiv.coe_addRight, Function.comp_apply] using
        (Equiv.sum_comp e (diophantineMinWeight q P))
    _ ≤ ((X / q + 1 : Nat) : Real) *
          ((P : Real) + q * Real.log q) := by
      gcongr
      exact sum_diophantineMinWeight_le q P

/-- After gcd cancellation, the initial-range sum is bounded by the complete
primitive-grid estimate. -/
theorem sum_range_diophantineMinWeight_neg_mul_le
    (c q P X : Nat) [NeZero q] :
    (∑ m ∈ Finset.range X,
        diophantineMinWeight q P (-((c * m : Nat) : ZMod q))) ≤
      (((X / reducedGridDenominator c q + 1 : Nat) : Real) *
        ((P : Real) + reducedGridDenominator c q *
          Real.log (reducedGridDenominator c q))) := by
  rw [sum_range_diophantineMinWeight_neg_mul_gcd_reduce]
  have hunit : IsUnit
      (-(reducedGridCoefficient c q :
        ZMod (reducedGridDenominator c q))) :=
    (reducedGridCoefficient_isUnit c q).neg
  simpa only [Nat.cast_mul, neg_mul] using
    (sum_range_diophantineMinWeight_mul_le
      (reducedGridDenominator c q) P X
      (-(reducedGridCoefficient c q :
        ZMod (reducedGridDenominator c q))) hunit)

/-- The positive interval `1,...,N` has the same reduced-grid block bound as
an initial interval of length `N`. -/
theorem sum_Icc_diophantineMinWeight_neg_mul_le
    (c q P N : Nat) [NeZero q] :
    (∑ m ∈ Finset.Icc 1 N,
        diophantineMinWeight q P (-((c * m : Nat) : ZMod q))) ≤
      (((N / reducedGridDenominator c q + 1 : Nat) : Real) *
        ((P : Real) + reducedGridDenominator c q *
          Real.log (reducedGridDenominator c q))) := by
  let Q := reducedGridDenominator c q
  let C := reducedGridCoefficient c q
  have hreduce :
      (∑ m ∈ Finset.Icc 1 N,
          diophantineMinWeight q P (-((c * m : Nat) : ZMod q))) =
        ∑ m ∈ Finset.Icc 1 N,
          diophantineMinWeight Q P (-((C * m : Nat) : ZMod Q)) := by
    apply Finset.sum_congr rfl
    intro m _
    exact diophantineMinWeight_neg_nat_mul_gcd_reduce c q P m
  rw [hreduce]
  have hinterval : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval, Finset.sum_Ico_eq_sum_range]
  have hunit : IsUnit (-(C : ZMod Q)) :=
    (reducedGridCoefficient_isUnit c q).neg
  have hbound := sum_range_diophantineMinWeight_affine_le Q P N
    (-(C : ZMod Q)) (-(C : ZMod Q)) hunit
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  push_cast
  ring

/-- The natural representative `120*a.val` realizes Chen's modular
coefficient `120*a`. -/
theorem oneHundredTwenty_mul_val_cast {q : Nat} [NeZero q] (a : ZMod q) :
    ((120 * a.val : Nat) : ZMod q) = (120 : ZMod q) * a := by
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- Denominator reduction preserves Chen's frequency `-(120*a*m)` pointwise. -/
theorem diophantineMinWeight_oneHundredTwenty_mul_gcd_reduce
    {q : Nat} [NeZero q] (a : ZMod q) (P m : Nat) :
    diophantineMinWeight q P (-((120 : ZMod q) * a * (m : ZMod q))) =
      diophantineMinWeight
        (reducedGridDenominator (120 * a.val) q) P
        (-((reducedGridCoefficient (120 * a.val) q :
          ZMod (reducedGridDenominator (120 * a.val) q)) *
            (m : ZMod (reducedGridDenominator (120 * a.val) q)))) := by
  rw [← oneHundredTwenty_mul_val_cast a]
  simpa only [← Nat.cast_mul] using
    (diophantineMinWeight_neg_nat_mul_gcd_reduce (120 * a.val) q P m)

/-- Chen's complete initial-range frequency sum obeys the reduced primitive-grid
bound. -/
theorem sum_range_diophantineMinWeight_oneHundredTwenty_mul_le
    {q : Nat} [NeZero q] (a : ZMod q) (P X : Nat) :
    (∑ m ∈ Finset.range X,
        diophantineMinWeight q P
          (-((120 : ZMod q) * a * (m : ZMod q)))) ≤
      (((X / reducedGridDenominator (120 * a.val) q + 1 : Nat) : Real) *
        ((P : Real) + reducedGridDenominator (120 * a.val) q *
          Real.log (reducedGridDenominator (120 * a.val) q))) := by
  have hsum := sum_range_diophantineMinWeight_neg_mul_le
    (120 * a.val) q P X
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro m _
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  norm_num

/-- Chen's positive product interval, in the multiplication order produced by
the product-fiber reindexing, obeys the reduced primitive-grid bound. -/
theorem sum_Icc_diophantineMinWeight_oneHundredTwenty_mul_le
    {q : Nat} [NeZero q] (a : ZMod q) (P N : Nat) :
    (∑ m ∈ Finset.Icc 1 N,
        diophantineMinWeight q P
          (-(a * (120 * (m : ZMod q))))) ≤
      (((N / reducedGridDenominator (120 * a.val) q + 1 : Nat) : Real) *
        ((P : Real) + reducedGridDenominator (120 * a.val) q *
          Real.log (reducedGridDenominator (120 * a.val) q))) := by
  have hsum := sum_Icc_diophantineMinWeight_neg_mul_le
    (120 * a.val) q P N
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

end Waring.Analytic
