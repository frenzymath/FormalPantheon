import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas

/-!
# Circular spacing of canonical rational points

This file proves the rational spacing facts used in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.5, pp. 175--178. The proof works through
the additive order of the rational difference on `UnitAddCircle`, so the
ordinary and wraparound distances are controlled simultaneously.
-/

namespace PrimesRestrictedDigits

private theorem ratCast_mem_unitInterval {r : Rat} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (r : Real) ∈ Set.Ico (0 : Real) 1 := by
  refine ⟨(Rat.cast_nonneg (K := Real)).mpr hr0, ?_⟩
  simpa using (Rat.cast_lt (K := Real)).mpr hr1

/-- Distinct rationals in the canonical half-open unit interval give distinct
points of `UnitAddCircle`. -/
theorem unitAddCircle_rat_ne_of_mem_Ico {r s : Rat}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) (hrs : r ≠ s) :
    ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle) := by
  intro hcircle
  have hreal : (r : Real) = (s : Real) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real))
      (by simpa using ratCast_mem_unitInterval hr0 hr1)
      (by simpa using ratCast_mem_unitInterval hs0 hs1)).mp hcircle
  exact hrs (Rat.cast_injective hreal)

private theorem ratDifference_addOrder (r s : Rat) :
    addOrderOf (((r - s : Rat) : Real) : UnitAddCircle) = (r - s).den := by
  simpa using
    (AddCircle.addOrderOf_coe_rat (p := (1 : Real)) (q := r - s))

/-- The circle distance between two distinct rational points is at least the
reciprocal of the canonical denominator of their difference. -/
theorem one_div_sub_den_le_dist_rat {r s : Rat}
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    1 / ((r - s).den : Real) ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  let u : UnitAddCircle := (((r - s : Rat) : Real) : UnitAddCircle)
  have huOrder : addOrderOf u = (r - s).den := by
    simpa [u] using ratDifference_addOrder r s
  have huNe : u ≠ 0 := by
    intro hu
    apply hrs
    have hsub :
        ((r : Real) : UnitAddCircle) - ((s : Real) : UnitAddCircle) = 0 := by
      simpa [u] using hu
    exact sub_eq_zero.mp hsub
  have huFin : IsOfFinAddOrder u := by
    apply addOrderOf_pos_iff.mp
    rw [huOrder]
    exact (r - s).den_pos
  have horder :=
    AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder huFin huNe
  rw [huOrder, nsmul_eq_mul] at horder
  have hdenPos : 0 < ((r - s).den : Real) := by positivity
  have hnorm : 1 / ((r - s).den : Real) ≤ norm u := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_comm] using horder
  simpa [u, dist_eq_norm] using hnorm

/-- Two distinct rational points on the unit circle are separated by the
reciprocal of the product of their canonical denominators. -/
theorem one_div_den_mul_den_le_dist_rat {r s : Rat}
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    1 / ((r.den : Real) * (s.den : Real)) ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  have hden : (r - s).den ≤ r.den * s.den :=
    Nat.le_of_dvd (Nat.mul_pos r.den_pos s.den_pos) (Rat.sub_den_dvd r s)
  have hdenReal : ((r - s).den : Real) ≤ (r.den : Real) * (s.den : Real) := by
    exact_mod_cast hden
  exact (one_div_le_one_div_of_le (by positivity) hdenReal).trans
    (one_div_sub_den_le_dist_rat hrs)

/-- If a positive natural divides both canonical denominators, it also
improves the circular spacing by that factor. -/
theorem natCast_div_den_mul_den_le_dist_rat {r s : Rat} {d : Nat}
    (_hd : 0 < d) (hdr : d ∣ r.den) (hds : d ∣ s.den)
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    (d : Real) / ((r.den : Real) * (s.den : Real)) ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  have hlcmPos : 0 < r.den.lcm s.den :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.den_nz s.den_nz)
  have hsubLe : (r - s).den ≤ r.den.lcm s.den :=
    Nat.le_of_dvd hlcmPos (Rat.sub_den_dvd_lcm r s)
  have hdGcd : d ∣ r.den.gcd s.den := Nat.dvd_gcd hdr hds
  have hdLeGcd : d ≤ r.den.gcd s.den :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left s.den r.den_pos) hdGcd
  have hmul : d * (r - s).den ≤ r.den * s.den := by
    calc
      d * (r - s).den ≤ d * r.den.lcm s.den := Nat.mul_le_mul_left d hsubLe
      _ ≤ r.den.gcd s.den * r.den.lcm s.den :=
        Nat.mul_le_mul_right (r.den.lcm s.den) hdLeGcd
      _ = r.den * s.den := Nat.gcd_mul_lcm r.den s.den
  have hfraction :
      (d : Real) / ((r.den : Real) * (s.den : Real)) ≤
        1 / ((r - s).den : Real) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast hmul
  exact hfraction.trans (one_div_sub_den_le_dist_rat hrs)

/-- Product-denominator spacing for distinct canonical representatives in
`[0, 1)`. -/
theorem one_div_den_mul_den_le_dist_rat_of_mem_Ico {r s : Rat}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) (hrs : r ≠ s) :
    1 / ((r.den : Real) * (s.den : Real)) ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) :=
  one_div_den_mul_den_le_dist_rat
    (unitAddCircle_rat_ne_of_mem_Ico hr0 hr1 hs0 hs1 hrs)

/-- Common-divisor spacing for distinct canonical representatives in
`[0, 1)`. -/
theorem natCast_div_den_mul_den_le_dist_rat_of_mem_Ico {r s : Rat} {d : Nat}
    (hd : 0 < d) (hdr : d ∣ r.den) (hds : d ∣ s.den)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) (hrs : r ≠ s) :
    (d : Real) / ((r.den : Real) * (s.den : Real)) ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) :=
  natCast_div_den_mul_den_le_dist_rat hd hdr hds
    (unitAddCircle_rat_ne_of_mem_Ico hr0 hr1 hs0 hs1 hrs)

private theorem ratDenProduct_le_sq {r s : Rat} {Q : Real}
    (hQ : 0 ≤ Q) (hr : (r.den : Real) ≤ Q) (hs : (s.den : Real) ≤ Q) :
    (r.den : Real) * (s.den : Real) ≤ Q ^ 2 := by
  rw [pow_two]
  exact mul_le_mul hr hs (by positivity) hQ

/-- Real denominator bounds turn product-denominator spacing into the Farey
scale `1 / Q^2`. -/
theorem one_div_sq_le_dist_rat_of_den_le {r s : Rat} {Q : Real}
    (hQ : 0 < Q) (hr : (r.den : Real) ≤ Q) (hs : (s.den : Real) ≤ Q)
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    1 / Q ^ 2 ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  have hproduct := ratDenProduct_le_sq hQ.le hr hs
  exact (one_div_le_one_div_of_le (by positivity) hproduct).trans
    (one_div_den_mul_den_le_dist_rat hrs)

/-- With a common positive denominator divisor, the real Farey scale improves
to `d / Q^2`. -/
theorem natCast_div_sq_le_dist_rat_of_den_le {r s : Rat} {d : Nat} {Q : Real}
    (hd : 0 < d) (hQ : 0 < Q) (hdr : d ∣ r.den) (hds : d ∣ s.den)
    (hr : (r.den : Real) ≤ Q) (hs : (s.den : Real) ≤ Q)
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    (d : Real) / Q ^ 2 ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  have hproduct := ratDenProduct_le_sq hQ.le hr hs
  have hfraction :
      (d : Real) / Q ^ 2 ≤ (d : Real) / ((r.den : Real) * (s.den : Real)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hproduct (by positivity)
  exact hfraction.trans (natCast_div_den_mul_den_le_dist_rat hd hdr hds hrs)

/-- Natural denominator bounds give the same `1 / Q^2` separation after
coercion to `Real`. -/
theorem one_div_natCast_sq_le_dist_rat_of_den_le {r s : Rat} {Q : Nat}
    (hQ : 0 < Q) (hr : r.den ≤ Q) (hs : s.den ≤ Q)
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    1 / (Q : Real) ^ 2 ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  apply one_div_sq_le_dist_rat_of_den_le (Q := (Q : Real))
  · exact_mod_cast hQ
  · exact_mod_cast hr
  · exact_mod_cast hs
  · exact hrs

/-- Natural denominator bounds and a common divisor give `d / Q^2`
separation after coercion to `Real`. -/
theorem natCast_div_natCast_sq_le_dist_rat_of_den_le
    {r s : Rat} {d Q : Nat}
    (hd : 0 < d) (hQ : 0 < Q) (hdr : d ∣ r.den) (hds : d ∣ s.den)
    (hr : r.den ≤ Q) (hs : s.den ≤ Q)
    (hrs : ((r : Real) : UnitAddCircle) ≠ ((s : Real) : UnitAddCircle)) :
    (d : Real) / (Q : Real) ^ 2 ≤
      dist ((r : Real) : UnitAddCircle) ((s : Real) : UnitAddCircle) := by
  apply natCast_div_sq_le_dist_rat_of_den_le (d := d) (Q := (Q : Real))
  · exact hd
  · exact_mod_cast hQ
  · exact hdr
  · exact hds
  · exact_mod_cast hr
  · exact_mod_cast hs
  · exact hrs

end PrimesRestrictedDigits
