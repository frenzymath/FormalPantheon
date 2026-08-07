import BoundedGaps.Maynard.ImprovedGPY.S2Restricted

noncomputable section

/-!
# Shift reindexing of the restricted S2 main term

Maynard2013v3, source lines 351--360, restricts the distinguished shift to
compatible pairs with `d_m = e_m = 1`.  The theorem below is the exact finite
sum interchange that exposes one arithmetic coefficient per shift.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance restrictedMainReindexDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def restrictedMainArithmeticCoefficient
  (H : Finset ℕ) (D : Finset (H → ℕ)) (W : ℕ)
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d : D, ∑ e : D.filter
    (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      if d.1 m = 1 ∧ e.1 m = 1 then
        (lambda d.1 * lambda e.1) /
          (Nat.totient (divisorPairModulus H W d.1 e.1) : ℝ)
      else 0

theorem compatiblePairRestrictedMainOuter_eq_shift_sum
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatiblePairRestrictedMainOuter H D R W v N lambda hD =
      ∑ m ∈ H.attach,
        (((primeCountTotal (2 * N + m.1 - 1) : ℝ) -
          (primeCountTotal (N + m.1 - 1) : ℝ)) *
          restrictedMainArithmeticCoefficient H D W lambda m) := by
  classical
  let term (d : D) (e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e)) (m : H) : ℝ :=
    if d.1 m = 1 ∧ e.1 m = 1 then
      shiftedPrimeProgressionIntervalMainTerm N
        (divisorPairModulus H W d.1 e.1)
        (divisorPairCrtResidue H R W v d.1 e.1
          (hD d.1 d.2)
          (hD e.1 (Finset.mem_filter.mp e.2).1)
          (Finset.mem_filter.mp e.2).2) m.1 *
        (lambda d.1 * lambda e.1)
    else 0
  have hleft :
      compatiblePairRestrictedMainOuter H D R W v N lambda hD =
        ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
            ∑ m ∈ H.attach, term d e m := by
    unfold compatiblePairRestrictedMainOuter
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rfl
  rw [hleft]
  simp only [Finset.univ_eq_attach]
  have hswap :
      (∑ d ∈ D.attach,
        ∑ e ∈ (D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
          ∑ m ∈ H.attach, term d e m) =
      ∑ m ∈ H.attach,
        ∑ d ∈ D.attach,
          ∑ e ∈ (D.filter
            (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
            term d e m := by
    calc
      (∑ d ∈ D.attach,
        ∑ e ∈ (D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
          ∑ m ∈ H.attach, term d e m) =
          ∑ d ∈ D.attach,
            ∑ m ∈ H.attach,
              ∑ e ∈ (D.filter
                (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
                term d e m := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro m hm
  unfold restrictedMainArithmeticCoefficient
  simp only [Finset.univ_eq_attach]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hme : d.1 m = 1 ∧ e.1 m = 1
  · simp [term, hme, shiftedPrimeProgressionIntervalMainTerm]
    ring
  · simp [term, hme]

end BoundedGaps.Maynard
