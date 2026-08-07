import BoundedGaps.Maynard.MaynardS2RestrictedYComparison

noncomputable section

/-!
# Scalarization of Maynard's S2 coordinate fiber

The main-face tuple is determined by its distinguished coordinate.  This file
reindexes that face by the scalar coordinate and specializes the result to the
smooth `maynardYValue`, giving the exact finite sum on Maynard2013v3, source
line 520, before partial summation is applied.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2CoordinateFiberScalarizationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def maynardS2OffCoordinateProduct
    (H : Finset ℕ) (m : H) (r : H → ℕ) : ℕ :=
  ∏ h ∈ Finset.univ.erase m, r h

def maynardS2CoordinateFiberSupport
    (H : Finset ℕ) (R W : ℕ) (m : H) (r : H → ℕ) : Finset ℕ :=
  (Finset.range R).filter fun u =>
    0 < u ∧
      u * maynardS2OffCoordinateProduct H m r < R ∧
      Squarefree u ∧
      Nat.Coprime u (W * maynardS2OffCoordinateProduct H m r)

theorem divisorTupleProduct_update_eq_mul_offCoordinateProduct
    {H : Finset ℕ} (m : H) (r : H → ℕ) (u : ℕ) :
    divisorTupleProduct H (Function.update r m u) =
      u * maynardS2OffCoordinateProduct H m r := by
  classical
  unfold divisorTupleProduct maynardS2OffCoordinateProduct
  rw [Finset.prod_update_of_mem (Finset.mem_univ m)]
  rw [show (Finset.univ : Finset H) \ {m} = Finset.univ.erase m by
    ext h
    simp]

theorem divisorTupleProduct_eq_offCoordinateProduct
    {H : Finset ℕ} (m : H) {r : H → ℕ} (hrm : r m = 1) :
    divisorTupleProduct H r = maynardS2OffCoordinateProduct H m r := by
  classical
  unfold divisorTupleProduct maynardS2OffCoordinateProduct
  rw [← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ m), hrm,
    one_mul]

theorem mem_maynardS2CoordinateFiberSupport_iff
    {H : Finset ℕ} {R W u : ℕ} (m : H) {r : H → ℕ}
    (hrm : r m = 1) :
    u ∈ maynardS2CoordinateFiberSupport H R W m r ↔
      u < R ∧ 0 < u ∧
        u * divisorTupleProduct H r < R ∧
        Squarefree u ∧ Nat.Coprime u (W * divisorTupleProduct H r) := by
  rw [maynardS2CoordinateFiberSupport, Finset.mem_filter, Finset.mem_range,
    divisorTupleProduct_eq_offCoordinateProduct m hrm]

theorem function_eq_update_of_maynardS2MainFace
    {H : Finset ℕ} (m : H) {r a : H → ℕ}
    (hface : IsMaynardS2MainFace m r a) :
    a = Function.update r m (a m) := by
  classical
  funext h
  by_cases hh : h = m
  · subst h
    simp
  · simp [hh, hface h hh]

theorem update_mem_maynardDivisorTupleSupport_iff
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) (u : ℕ) :
    Function.update r m u ∈ maynardDivisorTupleSupport H R W ↔
      u ∈ maynardS2CoordinateFiberSupport H R W m r := by
  classical
  let P := maynardS2OffCoordinateProduct H m r
  have hrProd : divisorTupleProduct H r = P :=
    divisorTupleProduct_eq_offCoordinateProduct m hrm
  have hPsq : Squarefree P := by
    rw [← hrProd]
    exact hr.2.2
  have hPW : Nat.Coprime P W := by
    rw [← hrProd]
    exact hr.2.1
  rw [maynardS2CoordinateFiberSupport, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · intro hu
    have huSupport := isMaynardDivisorTuple_of_mem_support hu
    have huBox := (mem_maynardDivisorTupleSupport_iff.mp hu).1
    have huData := (mem_maynardDivisorTupleBox_iff.mp huBox) m
    have hprod : divisorTupleProduct H (Function.update r m u) = u * P :=
      divisorTupleProduct_update_eq_mul_offCoordinateProduct m r u
    have huSq : Squarefree u := by
      simpa using huSupport.coordinate_squarefree m
    have huW : Nat.Coprime u W := by
      simpa using huSupport.coordinate_coprime_W m
    have huP : Nat.Coprime u P := by
      apply Nat.coprime_of_squarefree_mul
      rw [← hprod]
      exact huSupport.2.2
    have huR : u < R := by simpa using huData.2
    have huOne : 1 ≤ u := by simpa using huData.1
    have huPos : 0 < u := huOne
    have huCutoff : u * P < R := by
      rw [← hprod]
      exact huSupport.1
    exact ⟨huR, huPos, huCutoff, huSq, huW.mul_right huP⟩
  · rintro ⟨huR, huPos, huCutoff, huSq, huCop⟩
    have huParts : Nat.Coprime u W ∧ Nat.Coprime u P := by
      simpa [Nat.coprime_mul_iff_right] using huCop
    have hprod : divisorTupleProduct H (Function.update r m u) = u * P :=
      divisorTupleProduct_update_eq_mul_offCoordinateProduct m r u
    have hmaynard : IsMaynardDivisorTuple H R W (Function.update r m u) := by
      rw [IsMaynardDivisorTuple, hprod]
      exact ⟨huCutoff, huParts.1.mul_left hPW,
        (Nat.squarefree_mul huParts.2).mpr ⟨huSq, hPsq⟩⟩
    exact mem_maynardDivisorTupleSupport_iff.mpr
      ⟨hmaynard.mem_maynardDivisorTupleBox, hmaynard⟩

theorem maynardS2CoordinateFiberSum_eq_scalarSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    maynardS2CoordinateFiberSum H R W y m r =
      ∑ u ∈ maynardS2CoordinateFiberSupport H R W m r,
        y (Function.update r m u) / Nat.totient u := by
  classical
  let S := (maynardDivisorTupleSupport H R W).filter
    (IsMaynardS2MainFace m r)
  unfold maynardS2CoordinateFiberSum
  rw [← Finset.sum_filter]
  change (∑ a ∈ S, y a / Nat.totient (a m)) = _
  apply Finset.sum_bij (fun a _ => a m)
  · intro a ha
    have haSupport := (Finset.mem_filter.mp ha).1
    have hface := (Finset.mem_filter.mp ha).2
    apply (update_mem_maynardDivisorTupleSupport_iff m hr hrm (a m)).mp
    rw [← function_eq_update_of_maynardS2MainFace m hface]
    exact haSupport
  · intro a ha b hb hab
    have haFace := (Finset.mem_filter.mp ha).2
    have hbFace := (Finset.mem_filter.mp hb).2
    rw [function_eq_update_of_maynardS2MainFace m haFace,
      function_eq_update_of_maynardS2MainFace m hbFace, hab]
  · intro u hu
    let a := Function.update r m u
    have haSupport :=
      (update_mem_maynardDivisorTupleSupport_iff m hr hrm u).mpr hu
    have haFace : IsMaynardS2MainFace m r a := by
      intro h hh
      simp [a, hh]
    refine ⟨a, Finset.mem_filter.mpr ⟨haSupport, haFace⟩, ?_⟩
    simp [a]
  · intro a ha
    have hface := (Finset.mem_filter.mp ha).2
    rw [function_eq_update_of_maynardS2MainFace m hface]
    simp

theorem maynardS2CoordinateFiberSum_maynardYValue_eq_sourceSum
    {H : Finset ℕ} {R W : ℕ} {F : (H → ℝ) → ℝ}
    (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    maynardS2CoordinateFiberSum H R W (maynardYValue H R W F) m r =
      ∑ u ∈ maynardS2CoordinateFiberSupport H R W m r,
        ((ArithmeticFunction.moebius u : ℝ) ^ 2 /
          Nat.totient u) *
        F (Function.update
          (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R)) := by
  classical
  rw [maynardS2CoordinateFiberSum_eq_scalarSum m hr hrm]
  apply Finset.sum_congr rfl
  intro u hu
  have huSupport :=
    (update_mem_maynardDivisorTupleSupport_iff m hr hrm u).mpr hu
  have huMaynard := isMaynardDivisorTuple_of_mem_support huSupport
  have huSq : Squarefree u :=
    (Finset.mem_filter.mp hu).2.2.2.1
  have hmu : (ArithmeticFunction.moebius u : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one u).mp huSq
  have hcond : divisorTupleProduct H (Function.update r m u) < R ∧
      Nat.Coprime (divisorTupleProduct H (Function.update r m u)) W ∧
      Squarefree (divisorTupleProduct H (Function.update r m u)) := huMaynard
  have hpoint :
      (fun h => Real.log ((Function.update r m u) h) / Real.log R) =
        Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R) := by
    funext h
    by_cases hh : h = m
    · subst h
      simp
    · simp [hh]
  rw [maynardYValue, if_pos hcond, hmu, hpoint]
  ring

end BoundedGaps.Maynard
