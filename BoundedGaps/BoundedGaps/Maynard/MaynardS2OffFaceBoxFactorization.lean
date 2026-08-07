import BoundedGaps.Maynard.MaynardS2OffFaceBoxMajorant
import BoundedGaps.Maynard.MaynardYDiagonalCollisionMass

noncomputable section

/-!
# Factorization of Maynard's restricted S2 off-face boxes

Each independent witness box is factored into scalar coordinate masses and
bounded using the fixed-divisor rough tails. This formalizes the product
majorant in Maynard2013v3, source lines 431--434.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem maynardS2OffFaceTupleWeight_eq_coordinateProduct
    {H : Finset ℕ} (m : H) (r a : H → ℕ) :
    maynardS2OffFaceTupleWeight H m r a =
      ∏ h : H, if h = m then
        (1 : ℝ) / Nat.totient (a h)
      else (r h : ℝ) / (Nat.totient (a h) : ℝ) ^ 2 := by
  classical
  let f : H → ℝ := fun h => if h = m then
    (1 : ℝ) / Nat.totient (a h)
  else (r h : ℝ) / (Nat.totient (a h) : ℝ) ^ 2
  unfold maynardS2OffFaceTupleWeight
  calc
    ((1 : ℝ) / Nat.totient (a m)) *
        ∏ h ∈ Finset.univ.erase m,
          (r h : ℝ) / (Nat.totient (a h) : ℝ) ^ 2 =
        f m * ∏ h ∈ Finset.univ.erase m, f h := by
      congr 1
      · simp [f]
      · apply Finset.prod_congr rfl
        intro h hh
        have hne := (Finset.mem_erase.mp hh).1
        simp [f, hne]
    _ = ∏ h : H, f h :=
      Finset.mul_prod_erase Finset.univ f (Finset.mem_univ m)
    _ = _ := by rfl

theorem maynardS2OffFaceCoordinateBoxMass_eq_product
    {H : Finset ℕ} {R D : ℕ} {m j : H} {r : H → ℕ}
    (hjm : j ≠ m) :
    maynardS2OffFaceCoordinateBoxMass H R D m r j =
      ∏ h : H, if h = m then
        preSievedCoordinateInvTotientMass (primorial D) R
      else if h = j then
        (r h : ℝ) *
          preSievedFixedDivisorStrictTotientSquareSum D (r h) R
      else
        (r h : ℝ) *
          preSievedFixedDivisorTotientSquareSum D (r h) R := by
  classical
  let S : H → Finset ℕ := fun h =>
    if h = m then preSievedCommonCoordinateSupport (primorial D) R
    else if h = j then
      (preSievedFixedDivisorTotientSquareSupport D (r h) R).erase (r h)
    else preSievedFixedDivisorTotientSquareSupport D (r h) R
  let w : H → ℕ → ℝ := fun h n => if h = m then
    (1 : ℝ) / Nat.totient n
  else (r h : ℝ) / (Nat.totient n : ℝ) ^ 2
  unfold maynardS2OffFaceCoordinateBoxMass maynardS2OffFaceCoordinateBox
  change (∑ a ∈ Fintype.piFinset S,
      maynardS2OffFaceTupleWeight H m r a) = _
  calc
    (∑ a ∈ Fintype.piFinset S,
        maynardS2OffFaceTupleWeight H m r a) =
        ∑ a ∈ Fintype.piFinset S, ∏ h : H, w h (a h) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [maynardS2OffFaceTupleWeight_eq_coordinateProduct m r a]
    _ = ∏ h : H, ∑ n ∈ S h, w h n := by
      exact (Finset.prod_univ_sum S w).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h hh
      by_cases hhM : h = m
      · subst h
        simp [S, w, preSievedCoordinateInvTotientMass]
      · rw [if_neg hhM]
        by_cases hhJ : h = j
        · subst h
          unfold S w preSievedFixedDivisorStrictTotientSquareSum
          simp only [hjm, if_false, if_true]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        · rw [if_neg hhJ]
          unfold S w preSievedFixedDivisorTotientSquareSum
          simp only [hhM, if_false, hhJ]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring

theorem maynardS2GProduct_mul_offFaceCoordinateBoxMass_le_coordinateProduct
    {H : Finset ℕ} {R D : ℕ} {m j : H} {r : H → ℕ}
    (hD : 0 < D) (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) (hjm : j ≠ m) :
    (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceCoordinateBoxMass H R D m r j ≤
      ∏ h : H, if h = m then
        preSievedCoordinateInvTotientMass (primorial D) R
      else
        maynardS2ScalarArithmeticFactor (r h) *
          (if h = j then 8 * Real.exp 8 / (D : ℝ)
          else 1 + 8 * Real.exp 8 / (D : ℝ)) := by
  classical
  rw [maynardS2OffFaceCoordinateBoxMass_eq_product hjm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro h hh
    split_ifs <;>
      simp only [preSievedCoordinateInvTotientMass,
        preSievedFixedDivisorStrictTotientSquareSum,
        preSievedFixedDivisorTotientSquareSum] <;> positivity
  · intro h hh
    by_cases hhM : h = m
    · subst h
      simp [hrm, maynardS2G]
    · rw [if_neg hhM]
      by_cases hhJ : h = j
      · rw [if_pos hhJ, if_pos hhJ]
        have hstrict := preSievedFixedDivisorStrictTotientSquareSum_le
          (Q := R) hD
          (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)
        unfold maynardS2ScalarArithmeticFactor
        calc
          (maynardS2G (r h) : ℝ) *
              ((r h : ℝ) *
                preSievedFixedDivisorStrictTotientSquareSum D (r h) R) ≤
              (maynardS2G (r h) : ℝ) *
                ((r h : ℝ) *
                  (((1 : ℝ) / (Nat.totient (r h) : ℝ) ^ 2) *
                    (8 * Real.exp 8 / (D : ℝ)))) := by
            gcongr
          _ = ((maynardS2G (r h) : ℝ) * (r h : ℝ) /
                (Nat.totient (r h) : ℝ) ^ 2) *
                (8 * Real.exp 8 / (D : ℝ)) := by ring
          _ ≤ (if h = m then
                preSievedCoordinateInvTotientMass (primorial D) R
              else ((maynardS2G (r h) : ℝ) * (r h : ℝ) /
                (Nat.totient (r h) : ℝ) ^ 2) *
                (8 * Real.exp 8 / (D : ℝ))) := by simp [hhM]
      · rw [if_neg hhJ, if_neg hhJ]
        have htotal := preSievedFixedDivisorTotientSquareSum_le
          (Q := R) hD
          (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)
        unfold maynardS2ScalarArithmeticFactor
        calc
          (maynardS2G (r h) : ℝ) *
              ((r h : ℝ) *
                preSievedFixedDivisorTotientSquareSum D (r h) R) ≤
              (maynardS2G (r h) : ℝ) *
                ((r h : ℝ) *
                  (((1 : ℝ) / (Nat.totient (r h) : ℝ) ^ 2) *
                    (1 + 8 * Real.exp 8 / (D : ℝ)))) := by
            gcongr
          _ = ((maynardS2G (r h) : ℝ) * (r h : ℝ) /
                (Nat.totient (r h) : ℝ) ^ 2) *
                (1 + 8 * Real.exp 8 / (D : ℝ)) := by ring
          _ ≤ (if h = m then
                preSievedCoordinateInvTotientMass (primorial D) R
              else ((maynardS2G (r h) : ℝ) * (r h : ℝ) /
                (Nat.totient (r h) : ℝ) ^ 2) *
                (1 + 8 * Real.exp 8 / (D : ℝ))) := by simp [hhM]

theorem maynardS2GProduct_mul_offFaceCoordinateBoxMass_le_factored
    {H : Finset ℕ} {R D : ℕ} {m j : H} {r : H → ℕ}
    (hD : 0 < D) (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) (hjm : j ≠ m) :
    (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceCoordinateBoxMass H R D m r j ≤
      preSievedCoordinateInvTotientMass (primorial D) R *
        maynardS2MainFaceArithmeticFactor H m r *
          ∏ h ∈ Finset.univ.erase m,
            (if h = j then 8 * Real.exp 8 / (D : ℝ)
            else 1 + 8 * Real.exp 8 / (D : ℝ)) := by
  classical
  let M : ℝ := preSievedCoordinateInvTotientMass (primorial D) R
  let T : ℝ := 8 * Real.exp 8 / (D : ℝ)
  let C : ℝ := 1 + T
  let scalar : H → ℝ := fun h =>
    maynardS2ScalarArithmeticFactor (r h)
  let factor : H → ℝ := fun h => if h = m then M
    else scalar h * (if h = j then T else C)
  have hbound :=
    maynardS2GProduct_mul_offFaceCoordinateBoxMass_le_coordinateProduct
      hD hr hrm hjm
  change (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceCoordinateBoxMass H R D m r j ≤
      M * maynardS2MainFaceArithmeticFactor H m r *
        ∏ h ∈ Finset.univ.erase m, (if h = j then T else C)
  calc
    (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceCoordinateBoxMass H R D m r j ≤
        ∏ h : H, factor h := by
      simpa [factor, scalar, M, T, C] using hbound
    _ = factor m * ∏ h ∈ Finset.univ.erase m, factor h := by
      exact (Finset.mul_prod_erase Finset.univ factor
        (Finset.mem_univ m)).symm
    _ = M * ∏ h ∈ Finset.univ.erase m,
          (scalar h * (if h = j then T else C)) := by
      congr 1
      · simp [factor]
      · apply Finset.prod_congr rfl
        intro h hh
        have hne := (Finset.mem_erase.mp hh).1
        simp [factor, hne]
    _ = M * (∏ h ∈ Finset.univ.erase m, scalar h) *
          ∏ h ∈ Finset.univ.erase m,
            (if h = j then T else C) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = M * maynardS2MainFaceArithmeticFactor H m r *
          ∏ h ∈ Finset.univ.erase m,
            (if h = j then T else C) := by
      have hscalar : (∏ h ∈ Finset.univ.erase m, scalar h) =
          maynardS2MainFaceArithmeticFactor H m r := by
        unfold scalar maynardS2ScalarArithmeticFactor
          maynardS2MainFaceArithmeticFactor
        rfl
      rw [hscalar]

end BoundedGaps.Maynard
