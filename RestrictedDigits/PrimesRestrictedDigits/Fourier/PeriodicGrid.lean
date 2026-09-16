import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic reindexing of a periodic finite grid

This generic finite identity reduces an arbitrary real shift to one normalized cell offset. It
is used in the repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 10.3.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def finAddIntEquiv (N : Nat) [NeZero N] (z : Int) :
    Fin N ≃ Fin N :=
  (ZMod.finEquiv N).toEquiv.trans
    ((Equiv.addRight (z : ZMod N)).trans (ZMod.finEquiv N).toEquiv.symm)

theorem sum_fin_periodic_add_div_eq_fract
    (f : Real -> Real) (hf : Function.Periodic f 1)
    (N : Nat) [NeZero N] (beta : Real) :
    (∑ a : Fin N, f (beta + (a.val : Real) / N)) =
      ∑ a : Fin N,
        f ((Int.fract ((N : Real) * beta) + (a.val : Real)) / N) := by
  let z : Int := ⌊(N : Real) * beta⌋
  let rotate := finAddIntEquiv N z
  have hpoint (a : Fin N) :
      f (beta + (a.val : Real) / N) =
        f ((Int.fract ((N : Real) * beta) + ((rotate a).val : Real)) / N) := by
    have hfin (x : Fin N) :
        ZMod.finEquiv N x = (x.val : ZMod N) := by
      apply ZMod.val_injective N
      rw [ZMod.val_natCast_of_lt x.isLt]
      cases N with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    have hequiv :
        ZMod.finEquiv N (rotate a) =
          ZMod.finEquiv N a + (z : ZMod N) := by
      simp [rotate, finAddIntEquiv]
    have hcast :
        (((rotate a).val : Int) : ZMod N) =
          ((z + (a.val : Int) : Int) : ZMod N) := by
      rw [hfin, hfin] at hequiv
      simpa [Int.cast_add, add_comm] using hequiv
    have hdvd : (N : Int) ∣ z + (a.val : Int) - (rotate a).val :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        ((rotate a).val : Int) (z + (a.val : Int)) N).mp hcast
    obtain ⟨m, hm⟩ := hdvd
    have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hfloor := Int.floor_add_fract ((N : Real) * beta)
    change (z : Real) + Int.fract ((N : Real) * beta) =
      (N : Real) * beta at hfloor
    have hmReal :
        (z : Real) + (a.val : Real) - ((rotate a).val : Real) =
          (N : Real) * (m : Real) := by
      exact_mod_cast hm
    have hnum :
        (N : Real) * beta + (a.val : Real) =
          Int.fract ((N : Real) * beta) + ((rotate a).val : Real) +
            (N : Real) * (m : Real) := by
      nlinarith
    have harg :
        beta + (a.val : Real) / N =
          (Int.fract ((N : Real) * beta) + ((rotate a).val : Real)) / N + m := by
      calc
        beta + (a.val : Real) / N =
            ((N : Real) * beta + (a.val : Real)) / N := by
          field_simp [hN]
        _ = (Int.fract ((N : Real) * beta) + ((rotate a).val : Real) +
            (N : Real) * (m : Real)) / N := by rw [hnum]
        _ = (Int.fract ((N : Real) * beta) + ((rotate a).val : Real)) / N + m := by
          field_simp [hN]
    rw [harg]
    simpa using (hf.int_mul m)
      ((Int.fract ((N : Real) * beta) + ((rotate a).val : Real)) / N)
  calc
    (∑ a : Fin N, f (beta + (a.val : Real) / N)) =
        ∑ a : Fin N,
          f ((Int.fract ((N : Real) * beta) + ((rotate a).val : Real)) / N) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a
    _ = ∑ a : Fin N,
          f ((Int.fract ((N : Real) * beta) + (a.val : Real)) / N) := by
      exact Equiv.sum_comp rotate
        (fun a : Fin N =>
          f ((Int.fract ((N : Real) * beta) + (a.val : Real)) / N))

end PrimesRestrictedDigits
