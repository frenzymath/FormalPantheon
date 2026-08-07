import BoundedGaps.Maynard.ConcreteRadiusSeparation
import BoundedGaps.Maynard.ConcreteS2OuterCollision

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

set_option maxRecDepth 9000 in
set_option maxHeartbeats 1200000 in
theorem eventually_engelsmaS2OffFaceInnerShell_endpoint_good
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      ∀ j ∈ fractionalSimplexInnerGridIndex
          (engelsmaOffFaceFinset m) mesh,
      ∀ u ∈ engelsmaFractionalTupleShell
          (engelsmaOffFaceFinset m) alpha
            (fractionalGridLower mesh j)
            (fractionalGridUpper mesh j) N,
        1 < maynardS2CoordinateFiberEndpoint
          (engelsmaMaynardRadius alpha N)
          (divisorTupleProduct (engelsmaOffFaceFinset m) u) := by
  let H := engelsmaOffFaceFinset m
  let I := fractionalSimplexInnerGridIndex H mesh
  have hcell : ∀ j ∈ I, ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ engelsmaFractionalTupleShell H alpha
          (fractionalGridLower mesh j)
          (fractionalGridUpper mesh j) N,
        1 < maynardS2CoordinateFiberEndpoint
          (engelsmaMaynardRadius alpha N) (divisorTupleProduct H u) := by
    intro j hj
    let s : ℝ := ∑ h : H, fractionalGridUpper mesh j h
    let gamma : ℝ := (1 + s) / 2
    let beta : H → ℝ := fun h => fractionalGridUpper mesh j h / gamma
    have hjData := fractionalSimplexInnerGridIndex_data hmesh hj
    have hsNonneg : 0 ≤ s := by
      dsimp [s]
      apply Finset.sum_nonneg
      intro h hh
      exact (hjData.1 h).2.1.1
    have hsLt : s < 1 := by simpa [s] using hjData.2
    have hgammaPos : 0 < gamma := by
      dsimp [gamma]
      linarith
    have hgammaLt : gamma < 1 := by
      dsimp [gamma]
      linarith
    have halphaGamma : 0 < alpha * gamma := mul_pos halpha hgammaPos
    have hbetaNonneg : ∀ h : H, 0 ≤ beta h := by
      intro h
      dsimp [beta]
      exact div_nonneg (hjData.1 h).2.1.1 hgammaPos.le
    have hbetaSum : ∑ h : H, beta h < 1 := by
      have hsumBeta : (∑ h : H, beta h) = s / gamma := by
        dsimp [beta]
        rw [Finset.sum_div]
        rfl
      rw [hsumBeta]
      apply (div_lt_one hgammaPos).2
      dsimp [gamma]
      linarith
    have hbox :=
      eventually_engelsmaFractionalTupleBox_subset_preSievedSimplexTupleSupport
        halphaGamma beta hbetaNonneg hbetaSum
    have hsep := eventually_engelsmaMaynardRadius_exponent_lt_half
      halpha hgammaPos hgammaLt
    filter_upwards [hbox, hsep] with N hboxN hsepN u hu
    have huNewBox : u ∈ engelsmaFractionalTupleBox H
        (alpha * gamma) beta N := by
      rw [engelsmaFractionalTupleBox, squarefreeCoprimeTupleBox,
        Fintype.mem_piFinset]
      intro h
      have huShell : u ∈ squarefreeCoprimeTupleShell H
          (engelsmaMaynardModulus N)
          (fun h => engelsmaMaynardRadius
            (alpha * fractionalGridLower mesh j h) N)
          (fun h => engelsmaMaynardRadius
            (alpha * fractionalGridUpper mesh j h) N) := by
        simpa [engelsmaFractionalTupleShell] using hu
      have huh := Fintype.mem_piFinset.mp huShell h
      have huUpper := Finset.mem_sdiff.mp huh |>.1
      have hexponent : (alpha * gamma) * beta h =
          alpha * fractionalGridUpper mesh j h := by
        dsimp [beta]
        field_simp [hgammaPos.ne']
      simpa [hexponent] using huUpper
    have huPre := hboxN huNewBox
    have hprodLt : divisorTupleProduct H u <
        engelsmaMaynardRadius (alpha * gamma) N :=
      (mem_preSievedSimplexTupleSupport_iff.mp huPre).2
    have hprodPos : 0 < divisorTupleProduct H u := by
      unfold divisorTupleProduct
      apply Finset.prod_pos
      intro h hh
      exact (preSievedSimplexTupleSupport_coordinate huPre h).1
    have hprodPlus : divisorTupleProduct H u + 1 ≤
        engelsmaMaynardRadius (alpha * gamma) N := by
      omega
    have htwice : 2 * divisorTupleProduct H u + 2 ≤
        2 * engelsmaMaynardRadius (alpha * gamma) N := by
      omega
    have hmain : 2 * divisorTupleProduct H u + 2 ≤
        engelsmaMaynardRadius alpha N - 1 := by
      omega
    have hendpoint : 2 ≤ maynardS2CoordinateFiberEndpoint
        (engelsmaMaynardRadius alpha N) (divisorTupleProduct H u) := by
      unfold maynardS2CoordinateFiberEndpoint
      rw [Nat.le_div_iff_mul_le hprodPos]
      omega
    omega
  have hall := I.eventually_all.mpr hcell
  filter_upwards [hall] with N hN j hj u hu
  exact hN j hj u hu

end BoundedGaps.Maynard
