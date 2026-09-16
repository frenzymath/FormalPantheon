import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Translation of local divisor sums

This file packages the exact change of variables used when a local analytic
argument is centered at the origin but its zeros are recorded in global
coordinates.
-/

open Complex Metric

namespace PrimesRestrictedDigits

private lemma shift_mem_closedBall_iff (c w : Complex) (R : Real) :
    w ∈ closedBall 0 R ↔ w + c ∈ closedBall c R := by
  simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]

private lemma meromorphicOrderAt_add_shift
    (g : Complex → Complex) (c w : Complex) :
    meromorphicOrderAt (fun z : Complex => g (z + c)) w =
      meromorphicOrderAt g (w + c) := by
  change meromorphicOrderAt (g ∘ fun z : Complex => z + c) w = _
  apply meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop)
  simp

private lemma divisor_add_shift_apply
    (g : Complex → Complex) (c w : Complex) (R : Real)
    (hf : MeromorphicOn (fun z : Complex => g (z + c))
      (closedBall 0 R))
    (hg : MeromorphicOn g (closedBall c R)) :
    MeromorphicOn.divisor (fun z : Complex => g (z + c))
        (closedBall 0 R) w =
      MeromorphicOn.divisor g (closedBall c R) (w + c) := by
  rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def]
  by_cases hw : w ∈ closedBall 0 R
  · have hwc := (shift_mem_closedBall_iff c w R).mp hw
    rw [if_pos ⟨hf, hw⟩, if_pos ⟨hg, hwc⟩,
      meromorphicOrderAt_add_shift]
  · have hwc : w + c ∉ closedBall c R :=
      fun h => hw ((shift_mem_closedBall_iff c w R).mpr h)
    rw [if_neg (fun h => hw h.2), if_neg (fun h => hwc h.2)]

/-- Reindex a multiplicity-weighted local divisor sum from coordinates
centered at zero to coordinates centered at `c`. -/
theorem finsum_divisor_add_shift_eq
    (g : Complex → Complex) (c s : Complex) (R : Real)
    (hf : MeromorphicOn (fun z : Complex => g (z + c))
      (closedBall 0 R))
    (hg : MeromorphicOn g (closedBall c R)) :
    (∑ᶠ w : Complex,
      ((MeromorphicOn.divisor (fun z : Complex => g (z + c))
        (closedBall 0 R) w : Int) : Complex) / ((s - c) - w)) =
      ∑ᶠ rho : Complex,
        ((MeromorphicOn.divisor g
          (closedBall c R) rho : Int) : Complex) / (s - rho) := by
  have hDiv (w : Complex) := divisor_add_shift_apply g c w R hf hg
  calc
    _ = ∑ᶠ w : Complex,
        ((MeromorphicOn.divisor g
          (closedBall c R) (w + c) : Int) : Complex) /
            (s - (w + c)) := by
      apply finsum_congr
      intro w
      rw [← hDiv]
      congr 1
      ring
    _ = _ := by
      simpa only [Equiv.coe_addRight] using
        (finsum_comp_equiv (Equiv.addRight c)
          (f := fun rho : Complex =>
            ((MeromorphicOn.divisor g
              (closedBall c R) rho : Int) : Complex) / (s - rho)))

end PrimesRestrictedDigits
