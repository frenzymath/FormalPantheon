import BoundedGaps.Maynard.MaynardS2OffFaceBoxFactorization

noncomputable section

/-!
# Explicit bound for Maynard's restricted S2 off-face sum

The witness product and sum are evaluated, the main arithmetic factor is
bounded by one, and the logarithmic pre-sieved mean is inserted. This closes
the off-face estimate in Maynard2013v3, source lines 431--434.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

theorem prod_ite_one_witness_eq
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {j : ι}
    (hj : j ∈ s) (T C : ℝ) :
    (∏ h ∈ s, if h = j then T else C) =
      T * C ^ (s.card - 1) := by
  calc
    (∏ h ∈ s, if h = j then T else C) =
        (if j = j then T else C) *
          ∏ h ∈ s.erase j, (if h = j then T else C) := by
      exact (Finset.mul_prod_erase s
        (fun h => if h = j then T else C) hj).symm
    _ = T * ∏ _h ∈ s.erase j, C := by
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro h hh
        have hne := (Finset.mem_erase.mp hh).1
        simp [hne]
    _ = T * C ^ (s.erase j).card := by rw [Finset.prod_const]
    _ = T * C ^ (s.card - 1) := by rw [Finset.card_erase_of_mem hj]

theorem maynardS2MainFaceArithmeticFactor_mem_Icc
    {H : Finset ℕ} {R D : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    maynardS2MainFaceArithmeticFactor H m r ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hfactor : maynardS2MainFaceArithmeticFactor H m r =
      ∏ h ∈ Finset.univ.erase m,
        maynardS2ScalarArithmeticFactor (r h) := by
    unfold maynardS2MainFaceArithmeticFactor
      maynardS2ScalarArithmeticFactor
    rfl
  rw [hfactor]
  constructor
  · apply Finset.prod_nonneg
    intro h hh
    exact (maynardS2ScalarArithmeticFactor_mem_Icc
      (hr.coordinate_squarefree h)).1
  · apply Finset.prod_le_one
    · intro h hh
      exact (maynardS2ScalarArithmeticFactor_mem_Icc
        (hr.coordinate_squarefree h)).1
    · intro h hh
      exact (maynardS2ScalarArithmeticFactor_mem_Icc
        (hr.coordinate_squarefree h)).2

theorem abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_explicit
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r| ≤
      B * ((Finset.univ.erase m).card : ℝ) *
        preSievedCoordinateInvTotientMass (primorial D) R *
        (8 * Real.exp 8 / (D : ℝ)) *
        (1 + 8 * Real.exp 8 / (D : ℝ)) ^
          ((Finset.univ.erase m).card - 1) := by
  classical
  let s : Finset H := Finset.univ.erase m
  let G : ℝ := ∏ h : H, (maynardS2G (r h) : ℝ)
  let M : ℝ := preSievedCoordinateInvTotientMass (primorial D) R
  let A : ℝ := maynardS2MainFaceArithmeticFactor H m r
  let T : ℝ := 8 * Real.exp 8 / (D : ℝ)
  let C : ℝ := 1 + T
  let K : ℝ := T * C ^ (s.card - 1)
  have hmajor :=
    abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_boxMass
      m hr hB hyBound
  have hbox : G *
      (∑ j ∈ s, maynardS2OffFaceCoordinateBoxMass H R D m r j) ≤
        (s.card : ℝ) * (M * A * K) := by
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ s, G * maynardS2OffFaceCoordinateBoxMass H R D m r j) ≤
          ∑ _j ∈ s, M * A * K := by
        apply Finset.sum_le_sum
        intro j hj
        have hjm := (Finset.mem_erase.mp hj).1
        have hjBound :=
          maynardS2GProduct_mul_offFaceCoordinateBoxMass_le_factored
            hD hr hrm hjm
        calc
          G * maynardS2OffFaceCoordinateBoxMass H R D m r j ≤
              M * A * ∏ h ∈ s,
                (if h = j then T else C) := by
            simpa [G, M, A, T, C, s] using hjBound
          _ = M * A * K := by
            rw [prod_ite_one_witness_eq hj]
      _ = (s.card : ℝ) * (M * A * K) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hA := maynardS2MainFaceArithmeticFactor_mem_Icc m hr
  have hM : 0 ≤ M := by
    unfold M preSievedCoordinateInvTotientMass
    positivity
  have hT : 0 ≤ T := by unfold T; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  have hK : 0 ≤ K := by unfold K; positivity
  have hscale : 0 ≤ B * (s.card : ℝ) * M * K := by positivity
  calc
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r| ≤
        B * G *
          ∑ j ∈ s, maynardS2OffFaceCoordinateBoxMass H R D m r j := by
      simpa [G, s] using hmajor
    _ = B * (G *
          ∑ j ∈ s, maynardS2OffFaceCoordinateBoxMass H R D m r j) := by ring
    _ ≤ B * ((s.card : ℝ) * (M * A * K)) := by
      exact mul_le_mul_of_nonneg_left hbox hB
    _ = (B * (s.card : ℝ) * M * K) * A := by ring
    _ ≤ (B * (s.card : ℝ) * M * K) * 1 :=
      mul_le_mul_of_nonneg_left hA.2 hscale
    _ = B * (s.card : ℝ) * M * T * C ^ (s.card - 1) := by
      unfold K
      ring
    _ = _ := by rfl

theorem abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_log
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ}
    (hD : 0 < D) (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ u, |y u| ≤ B) :
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r| ≤
      B * ((Finset.univ.erase m).card : ℝ) *
        (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
          (1 + Real.log R)) *
        (8 * Real.exp 8 / (D : ℝ)) *
        (1 + 8 * Real.exp 8 / (D : ℝ)) ^
          ((Finset.univ.erase m).card - 1) := by
  have hbase :=
    abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_explicit
      m hD hr hrm hB hyBound
  have hpre : preSievedCoordinateInvTotientMass (primorial D) R ≤
      squarefreeCoprimeInvTotientMean (primorial D) R := by
    simpa [preSievedCoordinateInvTotientMass] using
      preSievedCoordinateInvTotientSum_le (primorial D) R
  have hmean := squarefreeCoprimeInvTotientMean_le_log
    (W := primorial D) (Q := R) (primorial_pos D) hWL
  have hM : preSievedCoordinateInvTotientMass (primorial D) R ≤
      8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R) := hpre.trans hmean
  have hscale : 0 ≤
      B * ((Finset.univ.erase m).card : ℝ) *
        (8 * Real.exp 8 / (D : ℝ)) *
        (1 + 8 * Real.exp 8 / (D : ℝ)) ^
          ((Finset.univ.erase m).card - 1) := by positivity
  calc
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r| ≤
        B * ((Finset.univ.erase m).card : ℝ) *
          preSievedCoordinateInvTotientMass (primorial D) R *
          (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1) := hbase
    _ = (B * ((Finset.univ.erase m).card : ℝ) *
          (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1)) *
        preSievedCoordinateInvTotientMass (primorial D) R := by ring
    _ ≤ (B * ((Finset.univ.erase m).card : ℝ) *
          (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1)) *
        (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
          (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left hM hscale
    _ = _ := by ring

end BoundedGaps.Maynard
