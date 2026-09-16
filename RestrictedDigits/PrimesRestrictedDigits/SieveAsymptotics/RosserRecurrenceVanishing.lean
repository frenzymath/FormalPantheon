import PrimesRestrictedDigits.SieveAsymptotics.RosserRecurrencePredicates

/-!
# Vanishing outside the finite Rosser recurrence ranges

The strict tuple cutoff makes a rank correction vanish once the corresponding beta-two cutoff
power is at most the level. These are the finite support facts used to recover the weak root
endpoints in Iwaniec's equations (4.4)--(4.5).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The nonnegative real root used in Iwaniec's weak outer endpoints. -/
noncomputable def rosserCutoffRoot
    (level : Real) (degree : Nat) : Real :=
  level ^ ((degree : Real)⁻¹)

/-- A weak lower root endpoint is exactly its natural-power inequality. -/
theorem rosserCutoffRoot_le_iff_pow_le
    {level x : Real} {degree : Nat}
    (hlevel : 0 ≤ level) (hx : 0 ≤ x) (hdegree : 0 < degree) :
    rosserCutoffRoot level degree ≤ x ↔ level ≤ x ^ degree := by
  have hdegreeReal : (0 : Real) < degree := by exact_mod_cast hdegree
  simpa [rosserCutoffRoot, Real.rpow_natCast] using
    (Real.rpow_inv_le_iff_of_pos hlevel hx hdegreeReal)

private theorem cast_list_prod_le_pow
    {xs : List Nat} {z : Real} (hz : 0 ≤ z)
    (hxs : ∀ p ∈ xs, (p : Real) ≤ z) :
    (xs.prod : Real) ≤ z ^ xs.length := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      have hp : (p : Real) ≤ z := hxs p (by simp)
      have htail : ∀ q ∈ xs, (q : Real) ≤ z := by
        intro q hq
        exact hxs q (by simp [hq])
      simp only [List.prod_cons, Nat.cast_mul, List.length_cons]
      rw [pow_succ']
      exact mul_le_mul hp (ih htail) (Nat.cast_nonneg _) hz

/-- A nonempty source subtuple lies strictly below the cubic cutoff power. -/
theorem rosserFailureCubic_lt_cutoffPow
    {P : Finset Nat} {z : Real} {xs : List Nat}
    (hprime : ∀ p ∈ P, p.Prime)
    (hsublist : List.Sublist xs (sieveFactorsBelow P z))
    (hne : xs ≠ []) :
    ((xs.dropLast.prod * xs.getLastD 1 ^ 3 : Nat) : Real) <
      z ^ (xs.length + 2) := by
  have hsource := sourceTuple_of_sublist_sieveFactorsBelow hsublist
  have hfactorPos : ∀ p ∈ xs, 0 < p := by
    intro p hp
    exact (hprime p (hsource.2 p hp).1).pos
  have hdropPosNat : 0 < xs.dropLast.prod := by
    apply List.prod_pos
    intro p hp
    exact hfactorPos p (List.mem_of_mem_dropLast hp)
  have hdropPos : (0 : Real) < xs.dropLast.prod := by
    exact_mod_cast hdropPosNat
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlastMem : (a :: tail).getLastD 1 ∈ a :: tail := by
    simpa only [List.getLastD_cons] using
      (List.getLastD_mem_cons (l := tail) (a := a))
  have hlastLt : (((a :: tail).getLastD 1 : Nat) : Real) < z :=
    (hsource.2 _ hlastMem).2
  have hz : 0 < z :=
    (show (0 : Real) < ((a :: tail).getLastD 1 : Nat) by
      exact_mod_cast hfactorPos _ hlastMem).trans hlastLt
  have hlastCube :
      (((a :: tail).getLastD 1 : Nat) : Real) ^ 3 < z ^ 3 :=
    pow_lt_pow_left₀ hlastLt (by positivity) (by norm_num)
  have hdropBound :
      (((a :: tail).dropLast.prod : Nat) : Real) ≤
        z ^ (a :: tail).dropLast.length := by
    apply cast_list_prod_le_pow hz.le
    intro p hp
    exact (hsource.2 p (List.mem_of_mem_dropLast hp)).2.le
  calc
    ((((a :: tail).dropLast.prod *
          (a :: tail).getLastD 1 ^ 3 : Nat) : Real)) =
        (((a :: tail).dropLast.prod : Nat) : Real) *
          (((a :: tail).getLastD 1 : Nat) : Real) ^ 3 := by
      push_cast
      ring
    _ < (((a :: tail).dropLast.prod : Nat) : Real) * z ^ 3 :=
      mul_lt_mul_of_pos_left hlastCube hdropPos
    _ ≤ z ^ (a :: tail).dropLast.length * z ^ 3 :=
      mul_le_mul_of_nonneg_right hdropBound (pow_nonneg hz.le _)
    _ = z ^ ((a :: tail).dropLast.length + 3) :=
      (pow_add z _ _).symm
    _ = z ^ ((a :: tail).length + 2) := by
      congr 1
      rw [List.length_dropLast]
      simp only [List.length_cons]
      omega

/-- An upper rank-`r` correction vanishes when
`z ^ (2 * r + 3) ≤ level`. The proof uses the strict cutoff `p < z`; no
sign condition on `nu` is needed. -/
theorem upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpower : z ^ (2 * r + 3) ≤ level) :
    upperRosserFailureSumAtRank P nu level z r = 0 := by
  classical
  rw [upperRosserFailureSumAtRank]
  have hfilter :
      (sieveFactorsBelow P z).sublists.filter
        (fun xs ↦ decide (IsUpperRosserFailure level r xs)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro xs hxs
    simp only [decide_eq_true_eq]
    intro hfailure
    have hsublist := List.mem_sublists.mp hxs
    have hne : xs ≠ [] := by
      simp [List.ne_nil_iff_length_pos, hfailure.1]
    have hcubic := upperRosserFailure_cubic hfailure
    have hstrict := rosserFailureCubic_lt_cutoffPow hprime hsublist hne
    rw [hfailure.1] at hstrict
    exact (not_lt_of_ge (hpower.trans hcubic)) hstrict
  rw [hfilter]
  simp

/-- A lower rank-`r` correction vanishes when
`z ^ (2 * r + 2) ≤ level`. -/
theorem lowerRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpower : z ^ (2 * r + 2) ≤ level) :
    lowerRosserFailureSumAtRank P nu level z r = 0 := by
  classical
  rw [lowerRosserFailureSumAtRank]
  have hfilter :
      (sieveFactorsBelow P z).sublists.filter
        (fun xs ↦ decide (IsLowerRosserFailure level r xs)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro xs hxs
    simp only [decide_eq_true_eq]
    intro hfailure
    have hsublist := List.mem_sublists.mp hxs
    have hne : xs ≠ [] := by
      simp [List.ne_nil_iff_length_pos, hfailure.1, hfailure.2.1]
    have hcubic := lowerRosserFailure_cubic hfailure
    have hstrict := rosserFailureCubic_lt_cutoffPow hprime hsublist hne
    rw [hfailure.2.1] at hstrict
    exact (not_lt_of_ge (hpower.trans hcubic)) hstrict
  rw [hfilter]
  simp

/-- All upper corrections through rank `R` vanish under the maximal-rank
cutoff condition. -/
theorem upperRosserFailurePartialSum_eq_zero_of_cutoffPow_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hz : 1 ≤ z)
    (hpower : z ^ (2 * R + 3) ≤ level) :
    upperRosserFailurePartialSum P nu level z R = 0 := by
  rw [upperRosserFailurePartialSum]
  apply Finset.sum_eq_zero
  intro r hr
  apply upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P nu level z r
    hprime
  apply (pow_le_pow_right₀ hz ?_).trans hpower
  simp only [Finset.mem_range] at hr
  omega

/-- All lower corrections through rank `R` vanish under the maximal-rank
cutoff condition. The rank range is empty when `R = 0`. -/
theorem lowerRosserFailurePartialSum_eq_zero_of_cutoffPow_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hz : 1 ≤ z)
    (hpower : z ^ (2 * R + 2) ≤ level) :
    lowerRosserFailurePartialSum P nu level z R = 0 := by
  rw [lowerRosserFailurePartialSum]
  apply Finset.sum_eq_zero
  intro r hr
  apply lowerRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P nu level z r
    hprime
  apply (pow_le_pow_right₀ hz ?_).trans hpower
  simp only [Finset.mem_Icc] at hr
  omega

end

end PrimesRestrictedDigits
