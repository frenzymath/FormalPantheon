import PrimesRestrictedDigits.BasicEstimates.BuchstabSteps

/-!
# The canonical Buchstab function

The least finite stage covering a given argument selects the canonical
Buchstab function. The construction and integral equation follow
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, Eqs. (7.37)--(7.39).
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- The least natural stage satisfying the upper cover `u <= n + 2`. -/
noncomputable def buchstabStage (u : Real) : Nat :=
  Nat.ceil (u - 2)

@[simp] theorem buchstabStage_le_iff (u : Real) (n : Nat) :
    buchstabStage u <= n <-> u <= (n : Real) + 2 := by
  rw [buchstabStage, Nat.ceil_le]
  constructor <;> intro h <;> linarith

@[simp] theorem buchstabStage_pos_iff (u : Real) :
    0 < buchstabStage u <-> 2 < u := by
  rw [buchstabStage, Nat.ceil_pos]
  constructor <;> intro h <;> linarith

theorem le_buchstabStage_add_two (u : Real) :
    u <= (buchstabStage u : Real) + 2 :=
  (buchstabStage_le_iff u (buchstabStage u)).mp le_rfl

/-- Later approximants agree with every earlier stage that already covers `u`. -/
theorem buchstabApprox_eq_of_le {m n : Nat} (hmn : m <= n) {u : Real}
    (h1 : 1 <= u) (hu : u <= (m : Real) + 2) :
    buchstabApprox n u = buchstabApprox m u := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hmnReal : (m : Real) <= n := by exact_mod_cast hmn
      calc
        buchstabApprox (n + 1) u = buchstabApprox n u :=
          buchstabApprox_succ_eq n h1 (by linarith)
        _ = buchstabApprox m u := ih

theorem buchstabApprox_eq_of_bounds (m n : Nat) {u : Real}
    (h1 : 1 <= u)
    (hm : u <= (m : Real) + 2) (hn : u <= (n : Real) + 2) :
    buchstabApprox m u = buchstabApprox n u := by
  rcases le_total m n with hmn | hnm
  · exact (buchstabApprox_eq_of_le hmn h1 hm).symm
  · exact buchstabApprox_eq_of_le hnm h1 hn

/-- Buchstab's function, selected from the stabilized finite approximants. -/
noncomputable def buchstabFunction (u : Real) : Real :=
  buchstabApprox (buchstabStage u) u

theorem buchstabFunction_eq_approx (n : Nat) {u : Real}
    (h1 : 1 <= u) (hu : u <= (n : Real) + 2) :
    buchstabFunction u = buchstabApprox n u := by
  exact buchstabApprox_eq_of_bounds (buchstabStage u) n h1
    (le_buchstabStage_add_two u) hu

theorem buchstabFunction_eq_inv {u : Real}
    (h1 : 1 <= u) (h2 : u <= 2) :
    buchstabFunction u = u⁻¹ := by
  rw [buchstabFunction_eq_approx 0 h1 (by simpa using h2)]
  rfl

@[simp] theorem buchstabFunction_one :
    buchstabFunction 1 = 1 := by
  rw [buchstabFunction_eq_inv (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem buchstabFunction_two :
    buchstabFunction 2 = 1 / 2 := by
  rw [buchstabFunction_eq_inv (by norm_num) le_rfl]
  norm_num

/-- The selected function is continuous throughout its source domain. -/
theorem continuousOn_buchstabFunction :
    ContinuousOn buchstabFunction (Set.Ici 1) := by
  intro u hu
  change (1 : Real) <= u at hu
  let n := buchstabStage u + 1
  have hun : u < (n : Real) + 2 := by
    dsimp [n]
    push_cast
    have hstage := le_buchstabStage_add_two u
    linarith
  have heq : buchstabFunction =ᶠ[nhdsWithin u (Set.Ici 1)]
      buchstabApprox n := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hun),
      self_mem_nhdsWithin] with v hvUpper hvLower
    exact buchstabFunction_eq_approx n hvLower hvUpper.le
  have happrox : ContinuousAt (buchstabApprox n) u :=
    (continuousOn_buchstabApprox n).continuousAt
      (isOpen_Ioi.mem_nhds (by linarith : (0 : Real) < u))
  exact happrox.continuousWithinAt.congr_of_eventuallyEq heq
    (buchstabFunction_eq_approx n hu hun.le)

/-- The integral form of the Buchstab equation, Eq. (7.39). -/
theorem mul_buchstabFunction_eq {u : Real} (hu : 2 <= u) :
    u * buchstabFunction u =
      1 + ∫ v in (1 : Real)..u - 1, buchstabFunction v := by
  rcases hu.eq_or_lt with rfl | hgt
  · norm_num
  · let n := buchstabStage u
    have hstage : u <= (n : Real) + 2 := by
      exact le_buchstabStage_add_two u
    have hfunction : buchstabFunction u = buchstabApprox (n + 1) u := by
      apply buchstabFunction_eq_approx (n + 1) (by linarith)
      push_cast
      linarith
    have hint : (∫ v in (1 : Real)..u - 1, buchstabFunction v) =
        ∫ v in (1 : Real)..u - 1, buchstabApprox n v := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
      apply buchstabFunction_eq_approx n hv.1
      exact hv.2.trans (by linarith)
    rw [hfunction, buchstabApprox_succ, if_neg (not_le.mpr hgt), hint]
    exact mul_div_cancel₀ _ (by linarith)

end PrimesRestrictedDigits
