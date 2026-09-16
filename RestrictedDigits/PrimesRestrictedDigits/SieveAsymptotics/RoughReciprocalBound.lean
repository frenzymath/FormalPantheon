import PrimesRestrictedDigits.BasicEstimates.ReciprocalPrimeChebyshev
import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Reciprocal sum over Maynard's strict rough carrier

The strict source support is enlarged only in the upper-bound direction to the weak prime
interval `[z,Y)`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def reciprocalMonoidHom : Nat →* Real :=
  (invMonoidHom : Real →* Real).comp (Nat.castRingHom Real).toMonoidHom

private theorem sum_inv_le_inversePrimeProduct
    (D s : Finset Nat)
    (hD0 : ∀ d ∈ D, d ≠ 0)
    (hfac : ∀ d ∈ D, ∀ p, Nat.Prime p → p ∣ d → p ∈ s) :
    (∑ d ∈ D, (d : Real)⁻¹) ≤
      ∏ p ∈ s.filter Nat.Prime, (1 - (p : Real)⁻¹)⁻¹ := by
  let e : ↑D ↪ Nat.factoredNumbers s :=
    { toFun := fun d ↦ ⟨d,
        Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr
          ⟨hD0 d d.property, fun p hp ↦ hfac d d.property p
            (Nat.prime_of_mem_primeFactors hp)
            (Nat.dvd_of_mem_primeFactors hp)⟩⟩
      inj' := fun x y h ↦ Subtype.ext (congrArg
        (fun z : Nat.factoredNumbers s ↦ (z : Nat)) h) }
  let T : Finset (Nat.factoredNumbers s) := D.attach.map e
  have hEuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := reciprocalMonoidHom) (fun {p} hp ↦ by
        change ‖((p : Real)⁻¹)‖ < 1
        have hpReal : (0 : Real) < p := by exact_mod_cast hp.pos
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpReal)]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) s
  calc
    (∑ d ∈ D, (d : Real)⁻¹) = ∑ m ∈ T, reciprocalMonoidHom m := by
      dsimp [T]
      rw [Finset.sum_map]
      change (∑ d ∈ D, (d : Real)⁻¹) =
        ∑ x ∈ D.attach, ((x : Nat) : Real)⁻¹
      exact (Finset.sum_attach D (fun d : Nat ↦ (d : Real)⁻¹)).symm
    _ ≤ ∑' m : Nat.factoredNumbers s, reciprocalMonoidHom m := by
      exact hEuler.1.of_norm.sum_le_tsum T (fun m hm ↦ by
        change 0 ≤ ((m : Nat) : Real)⁻¹
        positivity)
    _ = ∏ p ∈ s.filter Nat.Prime, (1 - (p : Real)⁻¹)⁻¹ :=
      hEuler.2.tsum_eq

/-- The reciprocal sum on the existing strict rough carrier is bounded by a
weak-endpoint inverse Euler product estimate. -/
theorem sum_inv_maynardStrictRoughCarrier_le
    (z Y : Real) (hz : 2 ≤ z) (hzY : z ≤ Y) :
    (∑ d ∈ maynardStrictRoughCarrier Y z, (d : Real)⁻¹) ≤
      Real.exp (16 / Real.log 2) *
        (Real.log Y / Real.log z) ^ (16 : Nat) := by
  let S := (naturalLeftClosedRightOpenInterval z Y).filter Nat.Prime
  have hfinite := sum_inv_le_inversePrimeProduct
    (maynardStrictRoughCarrier Y z) S (by
      intro d hd
      rw [mem_maynardStrictRoughCarrier] at hd
      omega) (by
        intro d hd p hp hpd
        rw [mem_maynardStrictRoughCarrier] at hd
        have hdp : p ≤ d := Nat.le_of_dvd (by omega) hpd
        have hdpReal : (p : Real) ≤ d := by exact_mod_cast hdp
        have hpY : (p : Real) < Y := hdpReal.trans_lt hd.2.1
        exact Finset.mem_filter.mpr
          ⟨mem_naturalLeftClosedRightOpenInterval.mpr
            ⟨(hd.2.2 p hp hpd).le, hpY⟩, hp⟩)
  have hfilter : S.filter Nat.Prime = S :=
    Finset.filter_eq_self.mpr
      (fun p hp ↦ (Finset.mem_filter.mp hp).2)
  rw [hfilter] at hfinite
  exact hfinite.trans (intervalPrimeInverseProduct_le z Y hz hzY)

/-- Source-parameter form of the strict rough reciprocal bound. -/
theorem sum_inv_maynardStrictRoughCarrier_rpow_le
    {X delta alpha : Real} (hX : 1 < X) (hdelta : 0 < delta)
    (hdeltaAlpha : delta ≤ alpha) (hcutoff : 2 ≤ X ^ delta) :
    (∑ d ∈ maynardStrictRoughCarrier (X ^ alpha) (X ^ delta),
      (d : Real)⁻¹) ≤
      Real.exp (16 / Real.log 2) * (alpha / delta) ^ (16 : Nat) := by
  have hX0 : 0 < X := by linarith
  have hlevel : X ^ delta ≤ X ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hX.le hdeltaAlpha
  have hbound := sum_inv_maynardStrictRoughCarrier_le
    (X ^ delta) (X ^ alpha) hcutoff hlevel
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hratio :
      Real.log (X ^ alpha) / Real.log (X ^ delta) = alpha / delta := by
    rw [Real.log_rpow hX0, Real.log_rpow hX0]
    field_simp [hdelta.ne', hlogX.ne']
  rw [hratio] at hbound
  exact hbound

end PrimesRestrictedDigits
