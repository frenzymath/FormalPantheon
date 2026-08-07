import BoundedGaps.Maynard.ImprovedGPY.S2ModulusSquarefree
import BoundedGaps.Maynard.MaynardLambdaTotientRegrouping

noncomputable section

/-!
# Totient factorization for the restricted S2 kernel

The CRT modulus is the pre-sieving modulus times the product of the
coordinate LCMs. Supported, cross-compatible divisor tuples make all these
factors coprime, so Euler's totient factors exactly.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2TotientDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def compatibleDivisorPairRestrictedTotientKernel
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d : D, ∑ e : D.filter (fun e => IsCrossCoordinateCoprime H d.1 e),
    if d.1 m = 1 ∧ e.1 m = 1 then
      (lambda d.1 * lambda e.1) /
        ∏ h : H, (Nat.totient (divisorTupleLcm H d.1 e.1 h) : ℝ)
    else 0

theorem totient_divisorPairModulus_eq_totient_mul_prod
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) :
    Nat.totient (divisorPairModulus H W d e) =
      Nat.totient W *
        ∏ h : H, Nat.totient (divisorTupleLcm H d e h) := by
  classical
  unfold divisorPairModulus
  rw [Nat.totient_mul]
  · congr 1
    apply totient_finsetProd_of_pairwise_coprime
    intro a ha b hb hab
    have hdd : Nat.Coprime (d a) (d b) := hd.coordinates_coprime hab
    have hee : Nat.Coprime (e a) (e b) := he.coordinates_coprime hab
    obtain ⟨hde, hed⟩ := hcross hab
    exact coprime_lcm_lcm_of_four hdd hde hed hee
  · apply Nat.Coprime.prod_right
    intro h hh
    have hWd : Nat.Coprime W (d h) := (hd.coordinate_coprime_W h).symm
    have hWe : Nat.Coprime W (e h) := (he.coordinate_coprime_W h).symm
    exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d h) (e h))
      (hWd.mul_right hWe)

set_option maxRecDepth 3000 in
theorem restrictedDivisorPairModulusTotientSum_eq_invTotient_mul
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W : ℕ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    (∑ d : D, ∑ e : D.filter
        (fun e => IsCrossCoordinateCoprime H d.1 e),
      if d.1 m = 1 ∧ e.1 m = 1 then
        (lambda d.1 * lambda e.1) /
          (Nat.totient (divisorPairModulus H W d.1 e.1) : ℝ)
      else 0) =
      (Nat.totient W : ℝ)⁻¹ *
        compatibleDivisorPairRestrictedTotientKernel H D lambda m := by
  classical
  unfold compatibleDivisorPairRestrictedTotientKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hdMem
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e heMem
  by_cases hm : d.1 m = 1 ∧ e.1 m = 1
  · rw [if_pos hm, if_pos hm]
    have heData := Finset.mem_filter.mp e.2
    have htotient := totient_divisorPairModulus_eq_totient_mul_prod
      (hD d.1 d.2) (hD e.1 heData.1) heData.2
    rw [htotient]
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · rw [if_neg hm, if_neg hm, mul_zero]

end BoundedGaps.Maynard
