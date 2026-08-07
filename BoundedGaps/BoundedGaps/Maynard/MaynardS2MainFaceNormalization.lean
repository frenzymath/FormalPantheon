import BoundedGaps.Maynard.MaynardS2WeightedMainFaceSplit

noncomputable section

/-!
# Normalization of Maynard's restricted S2 main face

The exact weighted main face is reduced to its one-coordinate fiber sum and
the arithmetic factor on Maynard2013v3, source line 438.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2MainFaceNormalizationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def maynardS2MainFaceArithmeticFactor
    (H : Finset ℕ) (m : H) (r : H → ℕ) : ℝ :=
  ∏ h ∈ Finset.univ.erase m,
    (maynardS2G (r h) : ℝ) * (r h : ℝ) /
      (Nat.totient (r h) : ℝ) ^ 2

noncomputable def maynardS2CoordinateFiberSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∑ a ∈ maynardDivisorTupleSupport H R W,
    if IsMaynardS2MainFace m r a then
      y a / Nat.totient (a m)
    else 0

theorem maynardS2_prefactor_mul_weightedMainFaceTerm_eq
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r a : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    (ha : IsMaynardDivisorTuple H R W a)
    (hrm : r m = 1) (hface : IsMaynardS2MainFace m r a) :
    (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
      ((y a / divisorTupleTotientProduct H a) *
        maynardS2WeightedFaceFactor H m r a) =
      maynardS2MainFaceArithmeticFactor H m r *
        (y a / Nat.totient (a m)) := by
  classical
  let off : Finset H := Finset.univ.erase m
  let prefactor : H → ℝ := fun h =>
    (ArithmeticFunction.moebius (r h) : ℝ) * maynardS2G (r h)
  let weighted : H → ℝ := fun h =>
    (ArithmeticFunction.moebius (r h) : ℝ) * (r h : ℝ) /
      Nat.totient (r h)
  let phi : H → ℝ := fun h => (Nat.totient (r h) : ℝ)
  have hprefactor : (∏ h : H, prefactor h) =
      ∏ h ∈ off, prefactor h := by
    have hm : prefactor m = 1 := by
      simp [prefactor, hrm, maynardS2G]
    exact (Finset.prod_erase (s := Finset.univ) hm).symm
  have htotient : divisorTupleTotientProduct H a =
      (Nat.totient (a m) : ℝ) * ∏ h ∈ off, phi h := by
    unfold divisorTupleTotientProduct
    calc
      (∏ h : H, (Nat.totient (a h) : ℝ)) =
          (Nat.totient (a m) : ℝ) *
            ∏ h ∈ Finset.univ.erase m, (Nat.totient (a h) : ℝ) := by
        exact (Finset.mul_prod_erase Finset.univ
          (fun h : H => (Nat.totient (a h) : ℝ))
          (Finset.mem_univ m)).symm
      _ = (Nat.totient (a m) : ℝ) * ∏ h ∈ off, phi h := by
        congr 1
        apply Finset.prod_congr rfl
        intro h hh
        have hne : h ≠ m := (Finset.mem_erase.mp hh).1
        rw [hface h hne]
  have hweighted : maynardS2WeightedFaceFactor H m r a =
      ∏ h ∈ off, weighted h := by
    unfold maynardS2WeightedFaceFactor
    apply Finset.prod_congr rfl
    intro h hh
    have hne : h ≠ m := (Finset.mem_erase.mp hh).1
    rw [hface h hne]
  have hnormalized :
      ((∏ h ∈ off, prefactor h) * (∏ h ∈ off, weighted h)) /
          (∏ h ∈ off, phi h) =
        maynardS2MainFaceArithmeticFactor H m r := by
    unfold maynardS2MainFaceArithmeticFactor
    rw [← Finset.prod_mul_distrib]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    have hmuSq :
        (ArithmeticFunction.moebius (r h) : ℝ) *
          ArithmeticFunction.moebius (r h) = 1 := by
      have hsquare := (squarefree_iff_moebius_sq_eq_one (r h)).mp
        (hr.coordinate_squarefree h)
      exact_mod_cast (by simpa [pow_two] using hsquare)
    have hphi : (Nat.totient (r h) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)))
    dsimp [prefactor, weighted, phi]
    field_simp [hphi]
    ring_nf at hmuSq
    rw [hmuSq]
    ring
  have hphiAm : (Nat.totient (a m) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (ha.coordinate_squarefree m).ne_zero)))
  have hphiOff : (∏ h ∈ off, phi h) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro h hh
    dsimp [phi]
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)))
  change (∏ h : H, prefactor h) *
      ((y a / divisorTupleTotientProduct H a) *
        maynardS2WeightedFaceFactor H m r a) =
    maynardS2MainFaceArithmeticFactor H m r *
      (y a / Nat.totient (a m))
  rw [hprefactor, htotient, hweighted, ← hnormalized]
  field_simp [hphiAm, hphiOff]

theorem maynardS2_prefactor_mul_weightedMainFace_eq
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
      maynardS2WeightedMainFaceSum H R W y m r =
      maynardS2MainFaceArithmeticFactor H m r *
        maynardS2CoordinateFiberSum H R W y m r := by
  classical
  unfold maynardS2WeightedMainFaceSum maynardS2CoordinateFiberSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have haSupport := isMaynardDivisorTuple_of_mem_support ha
  by_cases hface : IsMaynardS2MainFace m r a
  · rw [if_pos hface, if_pos hface]
    exact maynardS2_prefactor_mul_weightedMainFaceTerm_eq
      m hr haSupport hrm hface
  · simp [hface]

theorem maynardS2RestrictedYFromCoefficientFromY_eq_fiber_add_offFace
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m r =
      maynardS2MainFaceArithmeticFactor H m r *
          maynardS2CoordinateFiberSum H R W y m r +
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
          maynardS2WeightedOffFaceSum H R W y m r := by
  rw [maynardS2RestrictedYFromCoefficientFromY_eq_mainFace_add_offFace
    hy m hr hrm]
  rw [maynardS2_prefactor_mul_weightedMainFace_eq m hr hrm]

end BoundedGaps.Maynard
