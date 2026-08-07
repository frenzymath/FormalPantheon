import BoundedGaps.Maynard.MaynardS2OffFaceExplicitBound

noncomputable section

/-!
# Complete comparison for Maynard's restricted S2 Y-transform

The one-coordinate fiber is bounded by projection, and the main-factor and
off-face errors are combined into an explicit logarithmic envelope. This
formalizes `lmm:YjExpression` in Maynard2013v3, source lines 411--440.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2RestrictedYComparisonDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem abs_maynardS2CoordinateFiberSum_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) (r : H → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
      B * preSievedCoordinateInvTotientMass (primorial D) R := by
  classical
  let S := (maynardDivisorTupleSupport H R (primorial D)).filter
    (IsMaynardS2MainFace m r)
  let projection : (H → ℕ) → ℕ := fun a => a m
  have hinj : Set.InjOn projection S := by
    intro a ha b hb hab
    have haFace := (Finset.mem_filter.mp ha).2
    have hbFace := (Finset.mem_filter.mp hb).2
    funext h
    by_cases hh : h = m
    · subst h
      exact hab
    · rw [haFace h hh, hbFace h hh]
  have himage : S.image projection ⊆
      preSievedCommonCoordinateSupport (primorial D) R := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have haSupport := isMaynardDivisorTuple_of_mem_support
      (Finset.mem_filter.mp ha).1
    have haBox := (mem_maynardDivisorTupleSupport_iff.mp
      (Finset.mem_filter.mp ha).1).1
    have haBounds := (mem_maynardDivisorTupleBox_iff.mp haBox) m
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr haBounds.2, haBounds.1,
      haSupport.coordinate_squarefree m,
      haSupport.coordinate_coprime_W m⟩
  unfold maynardS2CoordinateFiberSum
  rw [← Finset.sum_filter]
  change |∑ a ∈ S, y a / Nat.totient (a m)| ≤ _
  calc
    |∑ a ∈ S, y a / Nat.totient (a m)| ≤
        ∑ a ∈ S, |y a / Nat.totient (a m)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, B / Nat.totient (a m) := by
      apply Finset.sum_le_sum
      intro a ha
      have hphi : 0 ≤ (Nat.totient (a m) : ℝ) := by positivity
      rw [abs_div, abs_of_nonneg hphi]
      gcongr
      exact hyBound a
    _ = ∑ n ∈ S.image projection, B / Nat.totient n := by
      exact (Finset.sum_image
        (f := fun n => B / (Nat.totient n : ℝ)) hinj).symm
    _ ≤ ∑ n ∈ preSievedCommonCoordinateSupport (primorial D) R,
          B / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro n hn hnNot
      positivity
    _ = B * preSievedCoordinateInvTotientMass (primorial D) R := by
      unfold preSievedCoordinateInvTotientMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem abs_maynardS2RestrictedY_sub_coordinateFiber_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r -
        maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
      B * ((Finset.univ.erase m).card : ℝ) *
        preSievedCoordinateInvTotientMass (primorial D) R *
        (8 / (D : ℝ) +
          (8 * Real.exp 8 / (D : ℝ)) *
            (1 + 8 * Real.exp 8 / (D : ℝ)) ^
              ((Finset.univ.erase m).card - 1)) := by
  let A := maynardS2MainFaceArithmeticFactor H m r
  let F := maynardS2CoordinateFiberSum H R (primorial D) y m r
  let E := (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
      maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r
  have hexact :=
    maynardS2RestrictedYFromCoefficientFromY_eq_fiber_add_offFace
      hy m hr hrm
  have hfactor := abs_maynardS2MainFaceArithmeticFactor_sub_one_le
    m hD hr
  have hfiber := abs_maynardS2CoordinateFiberSum_le
    (R := R) (D := D) m r hB hyBound
  have hoff :=
    abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_explicit
      m hD hr hrm hB hyBound
  change |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r - F| ≤ _
  rw [hexact]
  change |A * F + E - F| ≤ _
  have hdecomp : A * F + E - F = (A - 1) * F + E := by ring
  rw [hdecomp]
  calc
    |(A - 1) * F + E| ≤ |(A - 1) * F| + |E| := abs_add_le _ _
    _ = |A - 1| * |F| + |E| := by rw [abs_mul]
    _ ≤ (8 * ((Finset.univ.erase m).card : ℝ) / (D : ℝ)) *
          (B * preSievedCoordinateInvTotientMass (primorial D) R) +
        B * ((Finset.univ.erase m).card : ℝ) *
          preSievedCoordinateInvTotientMass (primorial D) R *
          (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1) := by
      apply add_le_add
      · exact mul_le_mul hfactor hfiber (abs_nonneg F) (by positivity)
      · exact hoff
    _ = B * ((Finset.univ.erase m).card : ℝ) *
        preSievedCoordinateInvTotientMass (primorial D) R *
        (8 / (D : ℝ) +
          (8 * Real.exp 8 / (D : ℝ)) *
            (1 + 8 * Real.exp 8 / (D : ℝ)) ^
              ((Finset.univ.erase m).card - 1)) := by ring

theorem abs_maynardS2RestrictedY_sub_coordinateFiber_le_log
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r -
        maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
      B * ((Finset.univ.erase m).card : ℝ) *
        (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
          (1 + Real.log R)) *
        (8 / (D : ℝ) +
          (8 * Real.exp 8 / (D : ℝ)) *
            (1 + 8 * Real.exp 8 / (D : ℝ)) ^
              ((Finset.univ.erase m).card - 1)) := by
  have hbase := abs_maynardS2RestrictedY_sub_coordinateFiber_le
    hy m hD hr hrm hB hyBound
  have hpre : preSievedCoordinateInvTotientMass (primorial D) R ≤
      squarefreeCoprimeInvTotientMean (primorial D) R := by
    simpa [preSievedCoordinateInvTotientMass] using
      preSievedCoordinateInvTotientSum_le (primorial D) R
  have hmean := squarefreeCoprimeInvTotientMean_le_log
    (W := primorial D) (Q := R) (primorial_pos D) hWL
  have hM : preSievedCoordinateInvTotientMass (primorial D) R ≤
      8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R) := hpre.trans hmean
  have hscale : 0 ≤ B * ((Finset.univ.erase m).card : ℝ) *
      (8 / (D : ℝ) +
        (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1)) := by positivity
  calc
    |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r -
        maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
        B * ((Finset.univ.erase m).card : ℝ) *
          preSievedCoordinateInvTotientMass (primorial D) R *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1)) := hbase
    _ = (B * ((Finset.univ.erase m).card : ℝ) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) *
        preSievedCoordinateInvTotientMass (primorial D) R := by ring
    _ ≤ (B * ((Finset.univ.erase m).card : ℝ) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) *
        (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
          (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left hM hscale
    _ = _ := by ring

theorem abs_maynardS2RestrictedY_sq_sub_coordinateFiber_sq_le_log
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |(maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r) ^ 2 -
        (maynardS2CoordinateFiberSum H R (primorial D) y m r) ^ 2| ≤
      2 * (B * preSievedCoordinateInvTotientMass (primorial D) R +
        B * ((Finset.univ.erase m).card : ℝ) *
          (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
            (1 + Real.log R)) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) *
        (B * ((Finset.univ.erase m).card : ℝ) *
          (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
            (1 + Real.log R)) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) := by
  let M := preSievedCoordinateInvTotientMass (primorial D) R
  let T := ((Finset.univ.erase m).card : ℝ) *
    (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
      (1 + Real.log R)) *
    (8 / (D : ℝ) +
      (8 * Real.exp 8 / (D : ℝ)) *
        (1 + 8 * Real.exp 8 / (D : ℝ)) ^
          ((Finset.univ.erase m).card - 1))
  let E := B * T
  let Y := maynardS2RestrictedYFromCoefficients H
    (maynardDivisorTupleSupport H R (primorial D))
    (maynardCoefficientFromY H R (primorial D) y) m r
  let F := maynardS2CoordinateFiberSum H R (primorial D) y m r
  have hM : 0 ≤ M := by
    dsimp [M]
    unfold preSievedCoordinateInvTotientMass
    positivity
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg hB hT
  have hYF : |Y - F| ≤ E := by
    dsimp [Y, F, E, T, M]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (abs_maynardS2RestrictedY_sub_coordinateFiber_le_log
        hy m hD hWL hr hrm hB hyBound)
  have hF : |F| ≤ B * M := by
    dsimp [F, M]
    simpa [mul_comm] using
      (abs_maynardS2CoordinateFiberSum_le
        (R := R) (D := D) m r hB hyBound)
  have hY : |Y| ≤ B * M + E := by
    calc
      |Y| = |(Y - F) + F| := by congr 1; ring
      _ ≤ |Y - F| + |F| := abs_add_le _ _
      _ ≤ E + B * M := add_le_add hYF hF
      _ = B * M + E := by ring
  have hsum : |Y + F| ≤ 2 * (B * M + E) := by
    calc
      |Y + F| ≤ |Y| + |F| := abs_add_le _ _
      _ ≤ (B * M + E) + B * M := add_le_add hY hF
      _ ≤ 2 * (B * M + E) := by
        have hBM : 0 ≤ B * M := mul_nonneg hB hM
        linarith
  have hsq : |Y ^ 2 - F ^ 2| ≤ 2 * (B * M + E) * E := by
    calc
      |Y ^ 2 - F ^ 2| = |(Y - F) * (Y + F)| := by
        congr 1
        ring
      _ = |Y - F| * |Y + F| := abs_mul _ _
      _ ≤ E * (2 * (B * M + E)) := by
        exact mul_le_mul hYF hsum (abs_nonneg _) (by positivity)
      _ = 2 * (B * M + E) * E := by ring
  simpa [Y, F, M, T, E, mul_assoc, mul_left_comm, mul_comm] using hsq

theorem abs_maynardS2RestrictedY_le_log
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤
      B * (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
        (1 + ((Finset.univ.erase m).card : ℝ) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) := by
  let M := preSievedCoordinateInvTotientMass (primorial D) R
  let A := 8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
    (1 + Real.log R)
  let E := 8 / (D : ℝ) +
    (8 * Real.exp 8 / (D : ℝ)) *
      (1 + 8 * Real.exp 8 / (D : ℝ)) ^
        ((Finset.univ.erase m).card - 1)
  let k : ℝ := (Finset.univ.erase m).card
  let Y := maynardS2RestrictedYFromCoefficients H
    (maynardDivisorTupleSupport H R (primorial D))
    (maynardCoefficientFromY H R (primorial D) y) m r
  let F := maynardS2CoordinateFiberSum H R (primorial D) y m r
  have hM : 0 ≤ M := by
    dsimp [M]
    unfold preSievedCoordinateInvTotientMass
    positivity
  have hMle : M ≤ A := by
    have hpre := preSievedCoordinateInvTotientSum_le
      (primorial D) R
    have hmean := squarefreeCoprimeInvTotientMean_le_log
      (W := primorial D) (Q := R) (primorial_pos D) hWL
    dsimp [M, A]
    exact hpre.trans hmean
  have hYF : |Y - F| ≤ B * k * A * E := by
    dsimp [Y, F, k, A, E]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (abs_maynardS2RestrictedY_sub_coordinateFiber_le_log
        hy m hD hWL hr hrm hB hyBound)
  have hF : |F| ≤ B * M := by
    dsimp [F, M]
    simpa [mul_comm] using
      (abs_maynardS2CoordinateFiberSum_le
        (R := R) (D := D) m r hB hyBound)
  have hFA : |F| ≤ B * A := by
    exact hF.trans (mul_le_mul_of_nonneg_left hMle hB)
  have hY : |Y| ≤ B * A + B * k * A * E := by
    calc
      |Y| = |(Y - F) + F| := by congr 1; ring
      _ ≤ |Y - F| + |F| := abs_add_le _ _
      _ ≤ B * k * A * E + B * A := add_le_add hYF hFA
      _ = B * A + B * k * A * E := by ring
  calc
    |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤
        B * A + B * k * A * E := hY
    _ = B * A * (1 + k * E) := by ring
    _ = B * (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
        (1 + ((Finset.univ.erase m).card : ℝ) *
          (8 / (D : ℝ) +
            (8 * Real.exp 8 / (D : ℝ)) *
              (1 + 8 * Real.exp 8 / (D : ℝ)) ^
                ((Finset.univ.erase m).card - 1))) := by
      rfl

end BoundedGaps.Maynard
