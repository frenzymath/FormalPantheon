import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Circular spacing on a fixed denominator grid

This is the exact `1 / q` spacing input for the first estimate in `MAYNARD-PRD-PUBLISHED`,
Lemma 10.5.
-/

namespace PrimesRestrictedDigits

/-- Distinct points `a/q`, with `a : Fin q`, are separated by at least
`1 / q` on `UnitAddCircle`. -/
theorem one_div_natCast_le_dist_fin_div
    {q : Nat} (hq : 0 < q) {a b : Fin q} (hab : a ≠ b) :
    1 / (q : Real) <=
      dist (((a.val : Real) / q : Real) : UnitAddCircle)
        (((b.val : Real) / q : Real) : UnitAddCircle) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let za : ZMod q := a.val
  let zb : ZMod q := b.val
  let u : UnitAddCircle := ZMod.toAddCircle (za - zb)
  have habZ : za ≠ zb := by
    intro hz
    apply hab
    apply Fin.ext
    have hzVal := congrArg ZMod.val hz
    simpa [za, zb, ZMod.val_natCast_of_lt a.isLt,
      ZMod.val_natCast_of_lt b.isLt] using hzVal
  have huNe : u ≠ 0 := by
    intro hu
    have hzero : za - zb = 0 := by
      exact (ZMod.toAddCircle_injective q) (by simpa [u] using hu)
    exact habZ (sub_eq_zero.mp hzero)
  have hqsmul : q • u = 0 := by
    dsimp [u]
    rw [← map_nsmul]
    have hzsmul : q • (za - zb) = 0 := by
      rw [nsmul_eq_mul]
      simp
    rw [hzsmul, map_zero]
  have huFin : IsOfFinAddOrder u := by
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q, hq, hqsmul⟩
  have horderDvd : addOrderOf u ∣ q :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hqsmul
  have horderLe : addOrderOf u <= q := Nat.le_of_dvd hq horderDvd
  have hcircle :=
    AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder huFin huNe
  rw [nsmul_eq_mul] at hcircle
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hnorm : 1 / (q : Real) <= ‖u‖ := by
    apply (div_le_iff₀ hqReal).mpr
    calc
      1 <= (addOrderOf u : Real) * ‖u‖ := hcircle
      _ <= (q : Real) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast horderLe) (norm_nonneg u)
      _ = ‖u‖ * (q : Real) := mul_comm _ _
  have huPoint :
      u = (((a.val : Real) / q : Real) : UnitAddCircle) -
        (((b.val : Real) / q : Real) : UnitAddCircle) := by
    dsimp [u, za, zb]
    rw [map_sub, ZMod.toAddCircle_natCast, ZMod.toAddCircle_natCast]
  rw [dist_eq_norm]
  rw [← huPoint]
  exact hnorm

end PrimesRestrictedDigits
