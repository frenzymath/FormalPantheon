import BoundedGaps.Maynard.MaynardS2CoordinateFiberScalarization
import BoundedGaps.Maynard.AugmentedReciprocalTotientLocalData
import BoundedGaps.Maynard.ReciprocalTotientCorrection
import BoundedGaps.Maynard.TwoScaleWeightedAbel

noncomputable section

/-!
The supported S2 coordinate fiber at its exact scalar endpoint.
Maynard2013v3, source line 520, normalizes by `log R` while the off-coordinate
product changes the summation endpoint.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable def maynardS2CoordinateFiberTest
    (H : Finset ℕ) (R : ℕ) (m : H) (r : H → ℕ)
    (F : (H → ℝ) → ℝ) (x : ℝ) : ℝ :=
  F (Function.update (fun h => Real.log (r h) / Real.log R) m x)

noncomputable def maynardS2CoordinateFiberEndpoint
    (R : ℕ) (P : ℕ) : ℕ := (R - 1) / P

theorem maynardS2OffCoordinateProduct_pos
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) :
    0 < maynardS2OffCoordinateProduct H m r := by
  unfold maynardS2OffCoordinateProduct
  apply Finset.prod_pos
  intro h hh
  exact Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero

theorem maynardS2CoordinateFiber_mem_support_iff_endpoint
    {H : Finset ℕ} {R W u : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hR : 0 < R) :
    u ∈ maynardS2CoordinateFiberSupport H R W m r ↔
      u ∈ Finset.Icc 1
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct H m r)) ∧
        Squarefree u ∧
        Nat.Coprime u (W * maynardS2OffCoordinateProduct H m r) := by
  let P := maynardS2OffCoordinateProduct H m r
  have hP : 0 < P := maynardS2OffCoordinateProduct_pos m r hr
  have hPone : 1 ≤ P := hP
  have hcutoff : ∀ v : ℕ, v * P < R ↔
      v ≤ maynardS2CoordinateFiberEndpoint R P := by
    intro v
    unfold maynardS2CoordinateFiberEndpoint
    rw [Nat.le_div_iff_mul_le hP]
    omega
  unfold maynardS2CoordinateFiberSupport
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨huR, huPos, huCutoff, huSq, huCop⟩
    refine ⟨Finset.mem_Icc.mpr ⟨huPos, (hcutoff u).mp huCutoff⟩,
      huSq, huCop⟩
  · rintro ⟨huEndpoint, huSq, huCop⟩
    have huPos : 0 < u := (Finset.mem_Icc.mp huEndpoint).1
    have huCutoff : u * P < R := (hcutoff u).mpr
      (Finset.mem_Icc.mp huEndpoint).2
    have huR : u < R := by
      have hmul : u ≤ u * P := by
        calc
          u = u * 1 := by simp
          _ ≤ u * P := Nat.mul_le_mul_left u hPone
      exact hmul.trans_lt huCutoff
    exact ⟨huR, huPos, huCutoff, huSq, huCop⟩

theorem maynardS2CoordinateFiberSupport_eq_endpointFilter
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hR : 0 < R) :
    maynardS2CoordinateFiberSupport H R W m r =
      (Finset.Icc 1
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r))).filter
        (fun u => Squarefree u ∧
          Nat.Coprime u (W * maynardS2OffCoordinateProduct H m r)) := by
  ext u
  simp only [Finset.mem_filter]
  exact maynardS2CoordinateFiber_mem_support_iff_endpoint m hr hR

noncomputable def maynardS2CoordinateFiberCoefficient
    (H : Finset ℕ) (W : ℕ) (m : H) (r : H → ℕ) (u : ℕ) : ℝ :=
  squarefreeCoprimeInvTotientAF
    (W * maynardS2OffCoordinateProduct H m r) u

theorem maynardS2CoordinateFiberCoefficient_zero
    {H : Finset ℕ} {W : ℕ} (m : H) (r : H → ℕ) :
    maynardS2CoordinateFiberCoefficient H W m r 0 = 0 := by
  exact (squarefreeCoprimeInvTotientAF
    (W * maynardS2OffCoordinateProduct H m r)).map_zero

theorem abelCumulative_maynardS2CoordinateFiberCoefficient_eq_mean
    {H : Finset ℕ} (W : ℕ) (m : H) (r : H → ℕ) (t : ℝ) :
    abelCumulative
        (maynardS2CoordinateFiberCoefficient H W m r) t =
      squarefreeCoprimeInvTotientMean
        (W * maynardS2OffCoordinateProduct H m r) ⌊t⌋₊ := by
  simpa [abelCumulative, maynardS2CoordinateFiberCoefficient] using
    (sum_squarefreeCoprimeInvTotientAF_eq_mean
      (W * maynardS2OffCoordinateProduct H m r) ⌊t⌋₊)

theorem abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_coprimeHarmonicSum_le
    {H : Finset ℕ} (W : ℕ) (m : H) (r : H → ℕ) (t : ℝ) :
    |abelCumulative
          (maynardS2CoordinateFiberCoefficient H W m r) t -
        coprimeHarmonicSum
          (W * maynardS2OffCoordinateProduct H m r) ⌊t⌋₊| ≤
      2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) := by
  rw [abelCumulative_maynardS2CoordinateFiberCoefficient_eq_mean]
  exact abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le
    (W * maynardS2OffCoordinateProduct H m r) ⌊t⌋₊

theorem maynardS2CoordinateFiberWeightedSum_eq_abelSum
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hR : 0 < R) {G : ℝ → ℝ} :
    (∑ u ∈ maynardS2CoordinateFiberSupport H R W m r,
        ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
          G (Real.log u / Real.log R)) =
      ∑ u ∈ Finset.Icc 0
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct H m r)),
        G (Real.log u / Real.log R) *
          maynardS2CoordinateFiberCoefficient H W m r u := by
  let P := maynardS2OffCoordinateProduct H m r
  let Q := maynardS2CoordinateFiberEndpoint R P
  have hsupport := maynardS2CoordinateFiberSupport_eq_endpointFilter m hr hR
  have hinterval : Finset.Icc 0 Q = insert 0 (Finset.Icc 1 Q) := by
    ext u
    simp
    omega
  rw [hsupport, hinterval, Finset.sum_insert (by simp)]
  rw [maynardS2CoordinateFiberCoefficient_zero m r, mul_zero, zero_add]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  have huData := Finset.mem_Icc.mp hu
  have huPos : u ≠ 0 := by omega
  by_cases huCond : Squarefree u ∧ Nat.Coprime u (W * P)
  · rw [if_pos huCond]
    change ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
      G (Real.log u / Real.log R) =
      G (Real.log u / Real.log R) *
        squarefreeCoprimeInvTotientAF (W * P) u
    rw [squarefreeCoprimeInvTotientAF_apply, if_neg huPos,
      if_pos huCond]
    have hmu : (ArithmeticFunction.moebius u : ℝ) ^ 2 = 1 := by
      exact_mod_cast (squarefree_iff_moebius_sq_eq_one u).mp huCond.1
    rw [hmu]
    ring
  · rw [if_neg huCond]
    change 0 = G (Real.log u / Real.log R) *
      squarefreeCoprimeInvTotientAF (W * P) u
    rw [squarefreeCoprimeInvTotientAF_apply, if_neg huPos,
      if_neg huCond]
    simp

theorem abs_maynardS2CoordinateFiberWeightedSum_sub_twoScaleNormalizedLogIntegral_le
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    {S E V : ℝ}
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct H m r))
    (hR : 1 < R) (hE : 0 ≤ E) {G : ℝ → ℝ}
    (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ)
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r)),
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r)))
    (hfInt : IntegrableOn
      (deriv (fun t => G (Real.log t / Real.log R)))
      (Set.Icc (1 : ℝ)
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r))))
    (hfNormInt : IntegrableOn
      (fun t => |deriv (fun t => G (Real.log t / Real.log R)) t|)
      (Set.Ioc (1 : ℝ)
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r))))
    (hmainInt : IntegrableOn
      (fun t => deriv (fun t => G (Real.log t / Real.log R)) t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ)
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct H m r))))
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ)
        (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct H m r)),
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient H W m r) t -
        S * Real.log t| ≤ E)
    (hvariation : (∫ t in Set.Ioc (1 : ℝ)
      (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct H m r)),
      |deriv (fun t => G (Real.log t / Real.log R)) t|) ≤ V) :
    |(∑ u ∈ maynardS2CoordinateFiberSupport H R W m r,
        ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
          G (Real.log u / Real.log R)) -
        S * Real.log R *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct H m r)) /
            Real.log R), G x)| ≤
      E * (|G (Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct H m r)) /
        Real.log R)| + V) := by
  let P := maynardS2OffCoordinateProduct H m r
  let Q := maynardS2CoordinateFiberEndpoint R P
  have hsum := maynardS2CoordinateFiberWeightedSum_eq_abelSum
    (R := R) (W := W) m hr (by omega) (G := G)
  rw [hsum]
  exact abs_weightedSum_sub_twoScaleNormalizedLogIntegral_le
    (Q := Q) (R := R) hQ hR
    (c := maynardS2CoordinateFiberCoefficient H W m r)
    (maynardS2CoordinateFiberCoefficient_zero m r) hE hG
    hfDeriv hfDerivInt hfInt hfNormInt hmainInt happrox hvariation

end BoundedGaps.Maynard
