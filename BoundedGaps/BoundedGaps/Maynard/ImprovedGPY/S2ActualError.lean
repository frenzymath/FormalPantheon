import BoundedGaps.Maynard.ImprovedGPY.S2ShiftedAggregation

noncomputable section

/-!
# The actual coefficient-weighted shifted S2 error

Maynard2013v3, in the proof of `lmm:S2Expression1` (source lines 351--370),
weights each surviving shifted CRT progression error by two sieve
coefficients. This file connects that exact finite error sum to the shifted
endpoint envelope.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance actualErrorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem compatiblePairShiftIndex_data
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {i : (((H → ℕ) × (H → ℕ)) × H)}
    (hi : i ∈ compatiblePairShiftIndex H D) :
    i.1.1 ∈ D ∧ i.1.2 ∈ D ∧
      IsCrossCoordinateCoprime H i.1.1 i.1.2 ∧
      (i.1.1 i.2 = 1 ∧ i.1.2 i.2 = 1) := by
  classical
  obtain ⟨hiProd, hreduce⟩ := Finset.mem_filter.mp hi
  obtain ⟨hiPairFiltered, _⟩ := Finset.mem_product.mp hiProd
  obtain ⟨hiPair, hcross⟩ := Finset.mem_filter.mp hiPairFiltered
  obtain ⟨hd, he⟩ := Finset.mem_product.mp hiPair
  exact ⟨hd, he, hcross, hreduce⟩

noncomputable def compatiblePairShiftCrtResidue
    (H : Finset ℕ) (D : Finset (H → ℕ)) (R W v : ℕ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (i : (((H → ℕ) × (H → ℕ)) × H)) : ℕ :=
  if hi : i ∈ compatiblePairShiftIndex H D then
    divisorPairCrtResidue H R W v i.1.1 i.1.2
      (hD i.1.1 (compatiblePairShiftIndex_data hi).1)
      (hD i.1.2 (compatiblePairShiftIndex_data hi).2.1)
      (compatiblePairShiftIndex_data hi).2.2.1
  else 0

def compatiblePairRestrictedAbsoluteErrorOuter
    (H : Finset ℕ) (D : Finset (H → ℕ)) (R W v N : ℕ)
    (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ d : D, ∑ e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
    ∑ h ∈ H.attach,
      if d.1 h = 1 ∧ e.1 h = 1 then
        |lambda d.1 * lambda e.1| *
          shiftedPrimeProgressionIntervalDiscrepancy N
            (divisorPairModulus H W d.1 e.1)
            (compatiblePairShiftCrtResidue H D R W v hD
              ((d.1, e.1), h)) h.1
      else 0

theorem abs_compatiblePairRestrictedErrorOuter_le_absoluteErrorOuter
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
      compatiblePairRestrictedAbsoluteErrorOuter H D R W v N lambda hD := by
  classical
  unfold compatiblePairRestrictedErrorOuter
    compatiblePairRestrictedAbsoluteErrorOuter
  calc
    |∑ d : D, ∑ e : D.filter
        (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
          restrictedCompatiblePairShiftErrorInner
            (v := v) (N := N) (hD d.1 d.2)
            (hD e.1 (Finset.mem_filter.mp e.2).1)
            (show IsCrossCoordinateCoprime H d.1 e.1 from
              (Finset.mem_filter.mp e.2).2) lambda| ≤
        ∑ d : D, |∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
            restrictedCompatiblePairShiftErrorInner
              (v := v) (N := N) (hD d.1 d.2)
              (hD e.1 (Finset.mem_filter.mp e.2).1)
              (show IsCrossCoordinateCoprime H d.1 e.1 from
                (Finset.mem_filter.mp e.2).2) lambda| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
        |restrictedCompatiblePairShiftErrorInner
          (v := v) (N := N) (hD d.1 d.2)
          (hD e.1 (Finset.mem_filter.mp e.2).1)
          (show IsCrossCoordinateCoprime H d.1 e.1 from
            (Finset.mem_filter.mp e.2).2) lambda| := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
        ∑ h ∈ H.attach,
          if d.1 h = 1 ∧ e.1 h = 1 then
            |lambda d.1 * lambda e.1| *
              shiftedPrimeProgressionIntervalDiscrepancy N
                (divisorPairModulus H W d.1 e.1)
                (compatiblePairShiftCrtResidue H D R W v hD
                  ((d.1, e.1), h)) h.1
          else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      unfold restrictedCompatiblePairShiftErrorInner
      calc
        |∑ h ∈ H.attach,
            if d.1 h = 1 ∧ e.1 h = 1 then
              shiftedPrimeProgressionIntervalError N
                (divisorPairModulus H W d.1 e.1)
                (divisorPairCrtResidue H R W v d.1 e.1
                  (hD d.1 d.2)
                  (hD e.1 (Finset.mem_filter.mp e.2).1)
                  (show IsCrossCoordinateCoprime H d.1 e.1 from
                    (Finset.mem_filter.mp e.2).2)) h.1 *
                (lambda d.1 * lambda e.1)
            else 0| ≤
            ∑ h ∈ H.attach,
              |if d.1 h = 1 ∧ e.1 h = 1 then
                shiftedPrimeProgressionIntervalError N
                  (divisorPairModulus H W d.1 e.1)
                  (divisorPairCrtResidue H R W v d.1 e.1
                    (hD d.1 d.2)
                    (hD e.1 (Finset.mem_filter.mp e.2).1)
                    (show IsCrossCoordinateCoprime H d.1 e.1 from
                      (Finset.mem_filter.mp e.2).2)) h.1 *
                  (lambda d.1 * lambda e.1)
              else 0| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ h ∈ H.attach,
            if d.1 h = 1 ∧ e.1 h = 1 then
              |lambda d.1 * lambda e.1| *
                shiftedPrimeProgressionIntervalDiscrepancy N
                  (divisorPairModulus H W d.1 e.1)
                  (compatiblePairShiftCrtResidue H D R W v hD
                    ((d.1, e.1), h)) h.1
            else 0 := by
          apply Finset.sum_congr rfl
          intro h hh
          by_cases hred : d.1 h = 1 ∧ e.1 h = 1
          · have hi : ((d.1, e.1), h) ∈ compatiblePairShiftIndex H D := by
              unfold compatiblePairShiftIndex
              apply Finset.mem_filter.mpr
              refine ⟨?_, hred⟩
              apply Finset.mem_product.mpr
              refine ⟨?_, Finset.mem_univ h⟩
              apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_product.mpr
                ⟨d.2, (Finset.mem_filter.mp e.2).1⟩,
                (Finset.mem_filter.mp e.2).2⟩
            have hresidue :
                compatiblePairShiftCrtResidue H D R W v hD ((d.1, e.1), h) =
                  divisorPairCrtResidue H R W v d.1 e.1
                    (hD d.1 d.2)
                    (hD e.1 (Finset.mem_filter.mp e.2).1)
                    (show IsCrossCoordinateCoprime H d.1 e.1 from
                      (Finset.mem_filter.mp e.2).2) := by
              unfold compatiblePairShiftCrtResidue
              rw [dif_pos hi]
            rw [if_pos hred, if_pos hred, hresidue, abs_mul]
            rw [mul_comm |shiftedPrimeProgressionIntervalError N
              (divisorPairModulus H W d.1 e.1)
              (divisorPairCrtResidue H R W v d.1 e.1
                (hD d.1 d.2)
                (hD e.1 (Finset.mem_filter.mp e.2).1)
                (show IsCrossCoordinateCoprime H d.1 e.1 from
                  (Finset.mem_filter.mp e.2).2)) h.1|]
            congr 1
          · simp [hred]

def compatiblePairShiftWeightedShiftedErrorSum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (R W v N : ℕ)
    (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ i ∈ compatiblePairShiftIndex H D,
    |lambda i.1.1 * lambda i.1.2| *
      shiftedPrimeProgressionIntervalDiscrepancy N
        (compatiblePairShiftModulus H W i)
        (compatiblePairShiftCrtResidue H D R W v hD i) i.2.1

theorem compatiblePairRestrictedAbsoluteErrorOuter_eq_weightedShiftedErrorSum
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatiblePairRestrictedAbsoluteErrorOuter H D R W v N lambda hD =
      compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD := by
  classical
  unfold compatiblePairRestrictedAbsoluteErrorOuter
    compatiblePairShiftWeightedShiftedErrorSum
  rw [compatiblePairShiftIndex]
  rw [Finset.sum_filter]
  symm
  calc
    (∑ a ∈ ((D ×ˢ D).filter (fun de =>
          IsCrossCoordinateCoprime H de.1 de.2)).product Finset.univ,
        if a.1.1 a.2 = 1 ∧ a.1.2 a.2 = 1 then
          |lambda a.1.1 * lambda a.1.2| *
            shiftedPrimeProgressionIntervalDiscrepancy N
              (compatiblePairShiftModulus H W a)
              (compatiblePairShiftCrtResidue H D R W v hD a) a.2.1
        else 0) =
        ∑ de ∈ (D ×ˢ D).filter (fun de =>
            IsCrossCoordinateCoprime H de.1 de.2),
          ∑ h : H,
            if de.1 h = 1 ∧ de.2 h = 1 then
              |lambda de.1 * lambda de.2| *
                shiftedPrimeProgressionIntervalDiscrepancy N
                  (compatiblePairShiftModulus H W (de, h))
                  (compatiblePairShiftCrtResidue H D R W v hD (de, h)) h.1
            else 0 :=
      Finset.sum_product
        ((D ×ˢ D).filter (fun de => IsCrossCoordinateCoprime H de.1 de.2))
        Finset.univ _
    _ = ∑ de ∈ D ×ˢ D,
          if IsCrossCoordinateCoprime H de.1 de.2 then
            ∑ h : H,
              if de.1 h = 1 ∧ de.2 h = 1 then
                |lambda de.1 * lambda de.2| *
                  shiftedPrimeProgressionIntervalDiscrepancy N
                    (compatiblePairShiftModulus H W (de, h))
                    (compatiblePairShiftCrtResidue H D R W v hD (de, h)) h.1
              else 0
          else 0 :=
      Finset.sum_filter
        (fun de : (H → ℕ) × (H → ℕ) =>
          IsCrossCoordinateCoprime H de.1 de.2) _
    _ = ∑ d ∈ D, ∑ e ∈ D,
          if IsCrossCoordinateCoprime H d e then
            ∑ h : H,
              if d h = 1 ∧ e h = 1 then
                |lambda d * lambda e| *
                  shiftedPrimeProgressionIntervalDiscrepancy N
                    (compatiblePairShiftModulus H W ((d, e), h))
                    (compatiblePairShiftCrtResidue H D R W v hD ((d, e), h)) h.1
              else 0
          else 0 :=
      Finset.sum_product D D _
    _ = ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
        ∑ h ∈ H.attach,
          if d.1 h = 1 ∧ e.1 h = 1 then
            |lambda d.1 * lambda e.1| *
              shiftedPrimeProgressionIntervalDiscrepancy N
                (divisorPairModulus H W d.1 e.1)
                (compatiblePairShiftCrtResidue H D R W v hD
                  ((d.1, e.1), h)) h.1
          else 0 := by
      simp only [Finset.univ_eq_attach H]
      unfold compatiblePairShiftModulus
      let g : (H → ℕ) → (H → ℕ) → ℝ := fun d e =>
        ∑ h ∈ H.attach,
          if d h = 1 ∧ e h = 1 then
            |lambda d * lambda e| *
              shiftedPrimeProgressionIntervalDiscrepancy N
                (divisorPairModulus H W d e)
                (compatiblePairShiftCrtResidue H D R W v hD ((d, e), h)) h.1
          else 0
      change (∑ d ∈ D, ∑ e ∈ D,
          if IsCrossCoordinateCoprime H d e then g d e else 0) =
        ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e), g d.1 e.1
      calc
        (∑ d ∈ D, ∑ e ∈ D,
            if IsCrossCoordinateCoprime H d e then g d e else 0) =
            ∑ d ∈ D, ∑ e ∈ D.filter
              (fun e : H → ℕ => IsCrossCoordinateCoprime H d e), g d e := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (Finset.sum_filter
            (fun e : H → ℕ => IsCrossCoordinateCoprime H d e) (g d)).symm
        _ = ∑ d ∈ D, ∑ e : D.filter
              (fun e : H → ℕ => IsCrossCoordinateCoprime H d e), g d e.1 := by
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_subtype
            (D.filter (fun e : H → ℕ => IsCrossCoordinateCoprime H d e))
            (fun _ => Iff.rfl) (g d)
        _ = ∑ d : D, ∑ e : D.filter
              (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e), g d.1 e.1 :=
          Finset.sum_subtype D (fun _ => Iff.rfl) _

theorem compatiblePairShiftWeightedShiftedErrorSum_le
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    compatiblePairShiftWeightedShiftedErrorSum
        H D R W v N lambda hD ≤
      L ^ 2 * compatiblePairShiftShiftedEndpointDiscrepancySum H D W N := by
  classical
  unfold compatiblePairShiftWeightedShiftedErrorSum
    compatiblePairShiftShiftedEndpointDiscrepancySum
  calc
    (∑ i ∈ compatiblePairShiftIndex H D,
        |lambda i.1.1 * lambda i.1.2| *
          shiftedPrimeProgressionIntervalDiscrepancy N
            (compatiblePairShiftModulus H W i)
            (compatiblePairShiftCrtResidue H D R W v hD i) i.2.1) ≤
        ∑ i ∈ compatiblePairShiftIndex H D,
          L ^ 2 *
            (maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
                (compatiblePairShiftModulus H W i) +
              maxProgressionDiscrepancy (N + i.2.1 - 1)
                (compatiblePairShiftModulus H W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      let hiData := compatiblePairShiftIndex_data hi
      let hdi := hD i.1.1 hiData.1
      let hei := hD i.1.2 hiData.2.1
      let hcrossi : IsCrossCoordinateCoprime H i.1.1 i.1.2 := hiData.2.2.1
      have hresidue : compatiblePairShiftCrtResidue H D R W v hD i =
          divisorPairCrtResidue H R W v i.1.1 i.1.2 hdi hei hcrossi := by
        unfold compatiblePairShiftCrtResidue
        rw [dif_pos hi]
      have herror : shiftedPrimeProgressionIntervalDiscrepancy N
          (compatiblePairShiftModulus H W i)
          (compatiblePairShiftCrtResidue H D R W v hD i) i.2.1 ≤
          maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
              (compatiblePairShiftModulus H W i) +
            maxProgressionDiscrepancy (N + i.2.1 - 1)
              (compatiblePairShiftModulus H W i) := by
        rw [hresidue]
        exact shiftedDivisorPairCrtResidue_intervalDiscrepancy_le_global_max
          hW hdi hei hcrossi hcoverage hv i.2 hiData.2.2.2.1
            hiData.2.2.2.2 hN
      have hcoef : |lambda i.1.1 * lambda i.1.2| ≤ L ^ 2 := by
        rw [abs_mul]
        calc
          |lambda i.1.1| * |lambda i.1.2| ≤ L * L :=
            mul_le_mul (hbound i.1.1 hiData.1) (hbound i.1.2 hiData.2.1)
              (abs_nonneg _) hL
          _ = L ^ 2 := by ring
      calc
        |lambda i.1.1 * lambda i.1.2| *
            shiftedPrimeProgressionIntervalDiscrepancy N
              (compatiblePairShiftModulus H W i)
              (compatiblePairShiftCrtResidue H D R W v hD i) i.2.1 ≤
            L ^ 2 * shiftedPrimeProgressionIntervalDiscrepancy N
              (compatiblePairShiftModulus H W i)
              (compatiblePairShiftCrtResidue H D R W v hD i) i.2.1 :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
        _ ≤ L ^ 2 *
            (maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
                (compatiblePairShiftModulus H W i) +
              maxProgressionDiscrepancy (N + i.2.1 - 1)
                (compatiblePairShiftModulus H W i)) :=
          mul_le_mul_of_nonneg_left herror (sq_nonneg L)
    _ = L ^ 2 *
        ∑ i ∈ compatiblePairShiftIndex H D,
          (maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
              (compatiblePairShiftModulus H W i) +
            maxProgressionDiscrepancy (N + i.2.1 - 1)
              (compatiblePairShiftModulus H W i)) := by
      rw [Finset.mul_sum]

theorem hasPrimeLevel_compatiblePairShiftWeightedShiftedErrorSum
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ N : ℕ, 0 < N →
        (∀ h : H, X₀ ≤ 2 * N + h.1 - 1) →
        (∀ h : H, X₀ ≤ N + h.1 - 1) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (2 * N + h.1 - 1)) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (N + h.1 - 1)) →
        compatiblePairShiftWeightedShiftedErrorSum
            H D R W v N lambda hD ≤
          L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
          ∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
  obtain ⟨C, hC, X₀, hX₀, hendpoint⟩ :=
    hasPrimeLevel_compatiblePairShiftShiftedEndpointDiscrepancySum
      hlevel A hA hW hD
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro N hN hupper hlower hcutUpper hcutLower
  exact (compatiblePairShiftWeightedShiftedErrorSum_le
    hW hD hcoverage hv hN hL hbound).trans
    (mul_le_mul_of_nonneg_left
      (hendpoint N hupper hlower hcutUpper hcutLower) (sq_nonneg L))

theorem abs_compatiblePairRestrictedErrorOuter_le_conditionalShiftedError
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ N : ℕ, 0 < N →
        (∀ h : H, X₀ ≤ 2 * N + h.1 - 1) →
        (∀ h : H, X₀ ≤ N + h.1 - 1) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (2 * N + h.1 - 1)) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (N + h.1 - 1)) →
        |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
          L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
          ∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
  obtain ⟨C, hC, X₀, hX₀, herror⟩ :=
    hasPrimeLevel_compatiblePairShiftWeightedShiftedErrorSum
      hlevel A hA hW hD hcoverage hv lambda L hL hbound
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro N hN hupper hlower hcutUpper hcutLower
  calc
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
        compatiblePairRestrictedAbsoluteErrorOuter H D R W v N lambda hD :=
      abs_compatiblePairRestrictedErrorOuter_le_absoluteErrorOuter hD
    _ = compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD :=
      compatiblePairRestrictedAbsoluteErrorOuter_eq_weightedShiftedErrorSum hD
    _ ≤ L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
        ∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) :=
      herror N hN hupper hlower hcutUpper hcutLower

theorem abs_compatiblePrimeWeightedPairSum_sub_restrictedOuterMain_le_conditionalShiftedError
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L)
    {N : ℕ} (hN : 0 < N) (hRN : R ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ((∀ h : H, X₀ ≤ 2 * N + h.1 - 1) →
        (∀ h : H, X₀ ≤ N + h.1 - 1) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (2 * N + h.1 - 1)) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (N + h.1 - 1)) →
        |compatiblePrimeWeightedPairSum H D v W N lambda -
            compatiblePairRestrictedMainOuter H D R W v N lambda hD| ≤
          L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
          ∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A))) := by
  obtain ⟨C, hC, X₀, hX₀, herror⟩ :=
    abs_compatiblePairRestrictedErrorOuter_le_conditionalShiftedError
      hlevel A hA hW hD hcoverage hv lambda L hL hbound
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro hupper hlower hcutUpper hcutLower
  calc
    |compatiblePrimeWeightedPairSum H D v W N lambda -
          compatiblePairRestrictedMainOuter H D R W v N lambda hD| =
        |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| := by
      rw [compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError
        hD hRN]
      ring_nf
    _ ≤ L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
        ∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) :=
      herror N hN hupper hlower hcutUpper hcutLower

end BoundedGaps.Maynard
