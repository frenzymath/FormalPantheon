import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # ConvexThreeAffineQuotient -/
open Set
namespace PrimesRestrictedDigits
private theorem hasDerivAt_eq_affine {f : Real → Real} (a b x : Real)
    (hf : ∀ z, f z = a + b * z) : HasDerivAt f b x := by
  have h : HasDerivAt (fun z : Real => a + b * z) b x := by
    simpa using (hasDerivAt_const_mul (x := x) b).const_add a
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)
theorem convexOn_x_mul_numerator_div_threeAffine
    {d theta h k : Real} {N N1 N2 N3 : Real -> Real}
    (hh : 0 <= h) (hk : k ∈ Icc (0 : Real) 1)
    (hden : ∀ X ∈ Icc 0 h,
      0 < d + X ∧ 0 < theta / 2 - k * X ∧
        0 < 3 * theta / 2 - (1 - k) * X)
    (hN0 : N 0 = 0)
    (hd0 : ∀ X ∈ Icc 0 h, HasDerivAt N (N1 X) X)
    (hd1 : ∀ X ∈ Icc 0 h, HasDerivAt N1 (N2 X) X)
    (hd2 : ∀ X ∈ Icc 0 h, HasDerivAt N2 (N3 X) X)
    (hN : ∀ X ∈ Icc 0 h, 0 <= N X)
    (hN2 : ∀ X ∈ Icc 0 h, 0 <= N2 X)
    (hN3 : ∀ X ∈ Icc 0 h, 0 <= N3 X) :
    ConvexOn Real (Icc 0 h)
      (fun X => X * N X /
        ((d + X) * (theta / 2 - k * X) *
          (3 * theta / 2 - (1 - k) * X))) := by
  let M := fun X => X * N1 X - N X
  let P := fun X => X ^ 2 * N2 X - 2 * X * N1 X + 2 * N X
  have hMderiv (X) (hX : X ∈ Icc 0 h) : HasDerivAt M (X * N2 X) X := by
    dsimp [M]
    exact (((hasDerivAt_id X).mul (hd1 X hX)).sub (hd0 X hX)).congr_deriv
      (by simp only [id_eq]; ring)
  have hPderiv (X) (hX : X ∈ Icc 0 h) : HasDerivAt P (X ^ 2 * N3 X) X := by
    dsimp [P]
    exact (((((hasDerivAt_pow 2 X).mul (hd2 X hX)).sub
      (((hasDerivAt_id X).const_mul 2).mul (hd1 X hX))).add
      ((hd0 X hX).const_mul 2)).congr_deriv (by simp only [id_eq]; ring))
  have hMmono : MonotoneOn M (Icc 0 h) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
      (fun X hX => (hMderiv X hX).continuousAt.continuousWithinAt)
      (fun X hX => (hMderiv X (interior_subset hX)).hasDerivWithinAt)
      (fun X hX => mul_nonneg (interior_subset hX).1 (hN2 X (interior_subset hX)))
  have hPmono : MonotoneOn P (Icc 0 h) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
      (fun X hX => (hPderiv X hX).continuousAt.continuousWithinAt)
      (fun X hX => (hPderiv X (interior_subset hX)).hasDerivWithinAt)
      (fun X hX => mul_nonneg (sq_nonneg X) (hN3 X (interior_subset hX)))
  let A := fun X : Real => X ^ 2 / (d + X)
  let B := fun X : Real => 1 / (theta / 2 - k * X)
  let C := fun X : Real => 1 / (3 * theta / 2 - (1 - k) * X)
  let R := fun X : Real => N X / X
  let A1 := fun X : Real => X * (2 * d + X) / (d + X) ^ 2
  let A2 := fun X : Real => 2 * d ^ 2 / (d + X) ^ 3
  let B1 := fun X : Real => k / (theta / 2 - k * X) ^ 2
  let B2 := fun X : Real => 2 * k ^ 2 / (theta / 2 - k * X) ^ 3
  let C1 := fun X : Real => (1 - k) / (3 * theta / 2 - (1 - k) * X) ^ 2
  let C2 := fun X : Real => 2 * (1 - k) ^ 2 /
    (3 * theta / 2 - (1 - k) * X) ^ 3
  let R1 := fun X : Real => M X / X ^ 2
  let R2 := fun X : Real => P X / X ^ 3
  let J := fun X => A X * B X * C X
  let J1 := fun X => A1 X * B X * C X + A X * B1 X * C X + A X * B X * C1 X
  let J2 := fun X => A2 X * B X * C X + 2 * A1 X * B1 X * C X +
    2 * A1 X * B X * C1 X + A X * B2 X * C X +
    2 * A X * B1 X * C1 X + A X * B X * C2 X
  let F := fun X => J X * R X
  let F1 := fun X => J1 X * R X + J X * R1 X
  let F2 := fun X => J2 X * R X + 2 * J1 X * R1 X + J X * R2 X
  have hEq : EqOn F (fun X => X * N X /
      ((d + X) * (theta / 2 - k * X) *
        (3 * theta / 2 - (1 - k) * X))) (Icc 0 h) := by
    intro X hX
    rcases hden X hX with ⟨hU, hV, hT⟩
    by_cases hX0 : X = 0
    · simp [F, J, A, B, C, R, hX0]
    · dsimp [F, J, A, B, C, R]
      field_simp [hX0, hU.ne', hV.ne', hT.ne']
  have hcont : ContinuousOn F (Icc 0 h) := by
    have hraw : ContinuousOn (fun X => X * N X /
        ((d + X) * (theta / 2 - k * X) *
          (3 * theta / 2 - (1 - k) * X))) (Icc 0 h) := by
      apply continuousOn_of_forall_continuousAt
      intro X hX
      rcases hden X hX with ⟨hU, hV, hT⟩
      have hUd : HasDerivAt (fun z => d + z) 1 X :=
        hasDerivAt_eq_affine d 1 X (fun z => by ring)
      have hVd : HasDerivAt (fun z => theta / 2 - k * z) (-k) X := by
        exact hasDerivAt_eq_affine (theta / 2) (-k) X (fun z => by ring)
      have hTd : HasDerivAt (fun z => 3 * theta / 2 - (1 - k) * z) (k - 1) X := by
        exact hasDerivAt_eq_affine (3 * theta / 2) (k - 1) X (fun z => by ring)
      exact ((hasDerivAt_id X).mul (hd0 X hX)).continuousAt.div
        (((hUd.mul hVd).mul hTd).continuousAt)
        (mul_ne_zero (mul_ne_zero hU.ne' hV.ne') hT.ne')
    exact hraw.congr hEq
  have hconvF : ConvexOn Real (Icc 0 h) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := F1) (f'' := F2)
      (convex_Icc 0 h) hcont
    · intro X hXi
      have hX := interior_subset hXi
      rcases hden X hX with ⟨hU, hV, hT⟩
      have hXp : 0 < X := (show X ∈ Ioo 0 h by simpa [interior_Icc] using hXi).1
      have hUd : HasDerivAt (fun z => d + z) 1 X :=
        hasDerivAt_eq_affine d 1 X (fun z => by ring)
      have hVd : HasDerivAt (fun z => theta / 2 - k * z) (-k) X :=
        hasDerivAt_eq_affine (theta / 2) (-k) X (fun z => by ring)
      have hTd : HasDerivAt (fun z => 3 * theta / 2 - (1 - k) * z) (k - 1) X :=
        hasDerivAt_eq_affine (3 * theta / 2) (k - 1) X (fun z => by ring)
      have hA : HasDerivAt A (A1 X) X := by
        dsimp [A, A1]
        exact ((hasDerivAt_pow 2 X).div hUd hU.ne').congr_deriv (by
          field_simp [hU.ne']; ring)
      have hB : HasDerivAt B (B1 X) X := by
        dsimp [B, B1]
        exact ((hasDerivAt_const X 1).div hVd hV.ne').congr_deriv (by
          field_simp [hV.ne']; ring)
      have hC : HasDerivAt C (C1 X) X := by
        dsimp [C, C1]
        exact ((hasDerivAt_const X 1).div hTd hT.ne').congr_deriv (by
          field_simp [hT.ne']; ring)
      have hR : HasDerivAt R (R1 X) X := by
        dsimp [R, R1, M]
        exact ((hd0 X hX).div (hasDerivAt_id X) hXp.ne').congr_deriv (by
          simp only [id_eq];
            field_simp [hXp.ne'])
      have hJ : HasDerivAt J (J1 X) X := by
        dsimp [J, J1]
        exact ((hA.mul hB).mul hC).congr_deriv (by
          simp only [ Pi.mul_apply]; ring)
      exact (hJ.mul hR).congr_deriv (by
        simp only [F1]) |>.hasDerivWithinAt
    · intro X hXi
      have hX := interior_subset hXi
      rcases hden X hX with ⟨hU, hV, hT⟩
      have hXp : 0 < X := (show X ∈ Ioo 0 h by simpa [interior_Icc] using hXi).1
      have hUd : HasDerivAt (fun z => d + z) 1 X :=
        hasDerivAt_eq_affine d 1 X (fun z => by ring)
      have hLd : HasDerivAt (fun z => 2 * d + z) 1 X :=
        hasDerivAt_eq_affine (2 * d) 1 X (fun z => by ring)
      have hVd : HasDerivAt (fun z => theta / 2 - k * z) (-k) X :=
        hasDerivAt_eq_affine (theta / 2) (-k) X (fun z => by ring)
      have hTd : HasDerivAt (fun z => 3 * theta / 2 - (1 - k) * z) (k - 1) X :=
        hasDerivAt_eq_affine (3 * theta / 2) (k - 1) X (fun z => by ring)
      have hA1 : HasDerivAt A1 (A2 X) X := by
        dsimp [A1, A2]
        exact (((hasDerivAt_id X).mul hLd).div (hUd.pow 2)
          (pow_ne_zero 2 hU.ne')).congr_deriv (by
            simp only [id_eq, Pi.mul_apply,   Pi.pow_apply];
              field_simp [hU.ne']; ring)
      have hB1 : HasDerivAt B1 (B2 X) X := by
        dsimp [B1, B2]
        exact ((hasDerivAt_const X k).div (hVd.pow 2)
          (pow_ne_zero 2 hV.ne')).congr_deriv (by
            simp only [    Pi.pow_apply]
            generalize hv : theta / 2 - k * X = v at hV ⊢
            field_simp [hV.ne']; ring)
      have hC1 : HasDerivAt C1 (C2 X) X := by
        dsimp [C1, C2]
        exact ((hasDerivAt_const X (1 - k)).div (hTd.pow 2)
          (pow_ne_zero 2 hT.ne')).congr_deriv (by
            simp only [    Pi.pow_apply]
            generalize ht : 3 * theta / 2 - (1 - k) * X = t at hT ⊢
            field_simp [hT.ne']; ring)
      have hR1 : HasDerivAt R1 (R2 X) X := by
        dsimp [R1, R2]
        exact ((hMderiv X hX).div (hasDerivAt_pow 2 X)
          (pow_ne_zero 2 hXp.ne')).congr_deriv (by
            dsimp [M, P]
            field_simp [hXp.ne']; ring)
      have hA : HasDerivAt A (A1 X) X := by
        dsimp [A, A1]
        exact ((hasDerivAt_pow 2 X).div hUd hU.ne').congr_deriv (by
          field_simp [hU.ne']; ring)
      have hB : HasDerivAt B (B1 X) X := by
        dsimp [B, B1]
        exact ((hasDerivAt_const X 1).div hVd hV.ne').congr_deriv (by
          field_simp [hV.ne']; ring)
      have hC : HasDerivAt C (C1 X) X := by
        dsimp [C, C1]
        exact ((hasDerivAt_const X 1).div hTd hT.ne').congr_deriv (by
          field_simp [hT.ne']; ring)
      have hR : HasDerivAt R (R1 X) X := by
        dsimp [R, R1, M]
        exact ((hd0 X hX).div (hasDerivAt_id X) hXp.ne').congr_deriv (by
          simp only [id_eq];
            field_simp [hXp.ne'])
      have hJ : HasDerivAt J (J1 X) X := by
        dsimp [J, J1]
        exact ((hA.mul hB).mul hC).congr_deriv (by
          simp only [ Pi.mul_apply]; ring)
      have hJ1 : HasDerivAt J1 (J2 X) X := by
        dsimp [J1, J2]
        exact ((((hA1.mul hB).mul hC).add ((hA.mul hB1).mul hC)).add
          ((hA.mul hB).mul hC1)).congr_deriv (by
            simp only [ Pi.mul_apply]; ring)
      exact ((hJ1.mul hR).add (hJ.mul hR1)).congr_deriv
        (by simp only [ F2,
          ]; ring) |>.hasDerivWithinAt
    · intro X hXi
      have hX := interior_subset hXi
      rcases hden X hX with ⟨hU, hV, hT⟩
      have hXp : 0 < X := (show X ∈ Ioo 0 h by simpa [interior_Icc] using hXi).1
      have hzero : (0 : Real) ∈ Icc 0 h := ⟨le_rfl, hh⟩
      have hd : 0 < d := by simpa using (hden 0 hzero).1
      have hM : 0 ≤ M X := by
        calc
          0 = M 0 := by simp [M, hN0]
          _ ≤ M X := hMmono hzero hX hX.1
      have hP : 0 ≤ P X := by
        calc
          0 = P 0 := by simp [P, hN0]
          _ ≤ P X := hPmono hzero hX hX.1
      have hA0 : 0 ≤ A X := by dsimp [A]; exact div_nonneg (sq_nonneg X) hU.le
      have hA10 : 0 ≤ A1 X := by
        dsimp [A1]
        exact div_nonneg (mul_nonneg hXp.le (add_nonneg (by positivity) hXp.le)) (sq_nonneg _)
      have hA20 : 0 ≤ A2 X := by dsimp [A2]; positivity
      have hB0 : 0 ≤ B X := by dsimp [B]; exact div_nonneg zero_le_one hV.le
      have hB10 : 0 ≤ B1 X := by dsimp [B1]; exact div_nonneg hk.1 (sq_nonneg _)
      have hB20 : 0 ≤ B2 X := by dsimp [B2]; positivity
      have hC0 : 0 ≤ C X := by dsimp [C]; exact div_nonneg zero_le_one hT.le
      have hC10 : 0 ≤ C1 X := by
        dsimp [C1]
        exact div_nonneg (sub_nonneg.mpr hk.2) (sq_nonneg _)
      have hC20 : 0 ≤ C2 X := by dsimp [C2]; positivity
      have hR0 : 0 ≤ R X := by dsimp [R]; exact div_nonneg (hN X hX) hXp.le
      have hR10 : 0 ≤ R1 X := by dsimp [R1]; exact div_nonneg hM (sq_nonneg _)
      have hR20 : 0 ≤ R2 X := by dsimp [R2]; positivity
      dsimp [F2, J, J1, J2]
      positivity
  exact hconvF.congr hEq
theorem convexOn_numerator_div_twoAffine
    {theta X lo hi : Real} {N Nk Nkk : Real -> Real}
    (hden : ∀ k ∈ Icc lo hi,
      0 < theta / 2 - k * X ∧
        0 < 3 * theta / 2 - (1 - k) * X)
    (hd0 : ∀ k ∈ Icc lo hi, HasDerivAt N (Nk k) k)
    (hd1 : ∀ k ∈ Icc lo hi, HasDerivAt Nk (Nkk k) k)
    (hN : ∀ k ∈ Icc lo hi, 0 <= N k)
    (hcombo : ∀ k ∈ Icc lo hi,
      0 <= Nkk k *
          ((theta / 2 - k * X) *
            (3 * theta / 2 - (1 - k) * X)) +
        2 * X * (theta - (1 - 2 * k) * X) * Nk k) :
    ConvexOn Real (Icc lo hi)
      (fun k => N k /
        ((theta / 2 - k * X) *
          (3 * theta / 2 - (1 - k) * X))) := by
  let p := fun k => (theta / 2 - k * X) * (3 * theta / 2 - (1 - k) * X)
  let Q := fun k => theta - (1 - 2 * k) * X
  let f1 := fun k => Nk k / p k + N k * X * Q k / p k ^ 2
  let f2 := fun k => Nkk k / p k + 2 * Nk k * X * Q k / p k ^ 2 +
    2 * N k * X ^ 2 / p k ^ 2 + 2 * N k * X ^ 2 * Q k ^ 2 / p k ^ 3
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f1) (f'' := f2) (convex_Icc lo hi)
  · intro k hk
    rcases hden k hk with ⟨hV, hT⟩
    have hVd : HasDerivAt (fun t => theta / 2 - t * X) (-X) k := by
      exact hasDerivAt_eq_affine (theta / 2) (-X) k (fun t => by ring)
    have hTd : HasDerivAt (fun t => 3 * theta / 2 - (1 - t) * X) X k := by
      exact hasDerivAt_eq_affine (3 * theta / 2 - X) X k (fun t => by ring)
    exact (((hd0 k hk).continuousAt.div (hVd.mul hTd).continuousAt
      (mul_ne_zero hV.ne' hT.ne')).continuousWithinAt)
  · intro k hki
    have hk := interior_subset hki
    rcases hden k hk with ⟨hV, hT⟩
    have hVd : HasDerivAt (fun t => theta / 2 - t * X) (-X) k :=
      hasDerivAt_eq_affine (theta / 2) (-X) k (fun t => by ring)
    have hTd : HasDerivAt (fun t => 3 * theta / 2 - (1 - t) * X) X k :=
      hasDerivAt_eq_affine (3 * theta / 2 - X) X k (fun t => by ring)
    have hp0 : p k ≠ 0 := by dsimp [p]; exact mul_ne_zero hV.ne' hT.ne'
    have hp : HasDerivAt p (-X * Q k) k := by
      dsimp [p, Q]
      exact (hVd.mul hTd).congr_deriv (by ring)
    exact ((hd0 k hk).div hp hp0).congr_deriv (by
      simp only [f1];
      field_simp [hp0]; ring) |>.hasDerivWithinAt
  · intro k hki
    have hk := interior_subset hki
    rcases hden k hk with ⟨hV, hT⟩
    have hVd : HasDerivAt (fun t => theta / 2 - t * X) (-X) k :=
      hasDerivAt_eq_affine (theta / 2) (-X) k (fun t => by ring)
    have hTd : HasDerivAt (fun t => 3 * theta / 2 - (1 - t) * X) X k :=
      hasDerivAt_eq_affine (3 * theta / 2 - X) X k (fun t => by ring)
    have hp0 : p k ≠ 0 := by dsimp [p]; exact mul_ne_zero hV.ne' hT.ne'
    have hp : HasDerivAt p (-X * Q k) k := by
      dsimp [p, Q]
      exact (hVd.mul hTd).congr_deriv (by ring)
    have hQd : HasDerivAt Q (2 * X) k := by
      dsimp [Q]
      exact hasDerivAt_eq_affine (theta - X) (2 * X) k (fun t => by ring)
    exact (((hd1 k hk).div hp hp0).add
      (((((hd0 k hk).mul (hasDerivAt_const k X)).mul hQd).div
        (hp.pow 2) (pow_ne_zero 2 hp0)))).congr_deriv (by
          simp only [f2,  Pi.mul_apply,   Pi.pow_apply];
          field_simp [hp0]; ring) |>.hasDerivWithinAt
  · intro k hki
    have hk := interior_subset hki
    rcases hden k hk with ⟨hV, hT⟩
    have hp : 0 < p k := by dsimp [p]; exact mul_pos hV hT
    have hfirst : 0 ≤ Nkk k / p k + 2 * Nk k * X * Q k / p k ^ 2 := by
      have hnum : 0 ≤ Nkk k * p k + 2 * X * Q k * Nk k := by
        simpa [p, Q] using hcombo k hk
      rw [show Nkk k / p k + 2 * Nk k * X * Q k / p k ^ 2 =
        (Nkk k * p k + 2 * X * Q k * Nk k) / p k ^ 2 by
          field_simp [hp.ne']]
      exact div_nonneg hnum (sq_nonneg (p k))
    have hNk0 := hN k hk
    have hthird : 0 ≤ 2 * N k * X ^ 2 / p k ^ 2 := by positivity
    have hfourth : 0 ≤ 2 * N k * X ^ 2 * Q k ^ 2 / p k ^ 3 := by positivity
    change 0 ≤ (Nkk k / p k + 2 * Nk k * X * Q k / p k ^ 2) +
      2 * N k * X ^ 2 / p k ^ 2 + 2 * N k * X ^ 2 * Q k ^ 2 / p k ^ 3
    exact add_nonneg (add_nonneg hfirst hthird) hfourth
end PrimesRestrictedDigits
