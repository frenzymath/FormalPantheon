import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Buchstab method-of-steps approximants

These are the finite-stage integral approximants underlying Eq. (7.39) of
`MONTGOMERY-VAUGHAN-MNT-I`. The canonical global function is a later slice.
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- The `n`th method-of-steps approximant to Buchstab's function. -/
noncomputable def buchstabApprox : Nat -> Real -> Real
  | 0, u => u⁻¹
  | n + 1, u =>
      if u <= 2 then u⁻¹
      else (1 + ∫ v in (1 : Real)..u - 1, buchstabApprox n v) / u

@[simp] theorem buchstabApprox_zero (u : Real) :
    buchstabApprox 0 u = u⁻¹ := rfl

@[simp] theorem buchstabApprox_succ (n : Nat) (u : Real) :
    buchstabApprox (n + 1) u =
      if u <= 2 then u⁻¹ else
        (1 + ∫ v in (1 : Real)..u - 1, buchstabApprox n v) / u := rfl

theorem buchstabApprox_of_le_two (n : Nat) {u : Real} (hu : u <= 2) :
    buchstabApprox n u = u⁻¹ := by
  cases n with
  | zero => rfl
  | succ n => rw [buchstabApprox_succ, if_pos hu]

@[simp] theorem buchstabApprox_one (n : Nat) :
    buchstabApprox n 1 = 1 := by
  rw [buchstabApprox_of_le_two n (by norm_num)]
  norm_num

@[simp] theorem buchstabApprox_two (n : Nat) :
    buchstabApprox n 2 = 1 / 2 := by
  rw [buchstabApprox_of_le_two n le_rfl]
  norm_num

/-- Consecutive approximants agree throughout the earlier stage's interval. -/
theorem buchstabApprox_succ_eq (n : Nat) {u : Real}
    (h1 : 1 <= u) (hu : u <= (n : Real) + 2) :
    buchstabApprox (n + 1) u = buchstabApprox n u := by
  induction n generalizing u with
  | zero =>
      norm_num at hu
      simp [buchstabApprox, hu]
  | succ n ih =>
      rw [buchstabApprox, buchstabApprox]
      by_cases h2 : u <= 2
      · simp [h2]
      · simp only [if_neg h2]
        congr 2
        apply intervalIntegral.integral_congr
        intro v hv
        apply ih
        · rw [Set.uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
          exact hv.1
        · rw [Set.uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
          push_cast at hu
          exact hv.2.trans (by linarith)

theorem buchstabApprox_succ_eqOn (n : Nat) :
    Set.EqOn (buchstabApprox (n + 1)) (buchstabApprox n)
      (Set.Icc 1 ((n : Real) + 2)) := by
  intro u hu
  exact buchstabApprox_succ_eq n hu.1 hu.2

private theorem continuousOn_integral_sub_one {f : Real -> Real}
    (hf : ContinuousOn f (Set.Ioi 0)) :
    ContinuousOn (fun u => ∫ v in (1 : Real)..u - 1, f v) (Set.Ici 2) := by
  intro u hu
  change (2 : Real) <= u at hu
  have hendpoint : 0 < u - 1 := by linarith
  have hfAll : ∀ v ∈ Set.Ioi (0 : Real), ContinuousAt f v := fun v hv =>
    hf.continuousAt (isOpen_Ioi.mem_nhds hv)
  have hfAt : ContinuousAt f (u - 1) := hfAll _ hendpoint
  have hint : IntervalIntegrable f volume 1 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply hf.mono
    intro v hv
    rw [Set.uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
    change (0 : Real) < v
    exact zero_lt_one.trans_le hv.1
  have hmeas : StronglyMeasurableAtFilter f (nhds (u - 1)) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hfAll _ hendpoint
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas hfAt
  have hshift : ContinuousAt (fun z : Real => z - 1) u :=
    continuousAt_id.sub continuousAt_const
  simpa only [Function.comp_def] using
    (hderiv.continuousAt.comp (f := fun z : Real => z - 1) hshift).continuousWithinAt

/-- Every finite-stage Buchstab approximant is continuous on the positive reals. -/
theorem continuousOn_buchstabApprox (n : Nat) :
    ContinuousOn (buchstabApprox n) (Set.Ioi 0) := by
  induction n with
  | zero =>
      change ContinuousOn (fun u : Real => u⁻¹) (Set.Ioi 0)
      exact continuousOn_id.inv₀ fun u hu => by
        change (0 : Real) < u at hu
        exact hu.ne'
  | succ n ih =>
      rw [continuousOn_iff_continuous_restrict]
      change Continuous (fun u : Set.Ioi (0 : Real) =>
        if (u : Real) <= 2 then (u : Real)⁻¹
        else (1 + ∫ v in (1 : Real)..(u : Real) - 1,
          buchstabApprox n v) / (u : Real))
      apply continuous_if_le continuous_subtype_val continuous_const
      · exact (continuous_subtype_val.inv₀ fun u => ne_of_gt u.property).continuousOn
      · have hg : ContinuousOn
            (fun u => (1 + ∫ v in (1 : Real)..u - 1,
              buchstabApprox n v) / u) (Set.Ici 2) := by
          apply ContinuousOn.div₀
          · exact continuousOn_const.add (continuousOn_integral_sub_one ih)
          · exact continuousOn_id
          · intro u hu
            change (2 : Real) <= u at hu
            linarith
        exact hg.comp continuous_subtype_val.continuousOn (by
          intro u hu
          exact hu)
      · intro u hu
        have huTwo : (u : Real) = 2 := hu
        norm_num [huTwo]

end PrimesRestrictedDigits
