import BoundedGaps.BombieriVinogradov.Analytic.MaximalBilinearConclusion
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermDyadic

/-!
# Maximal energy bound for Vaughan's fourth term

This file lifts the exact dyadic decomposition of the fourth Vaughan term to
per-character endpoint maxima and applies the sparse maximal bilinear large
sieve to every active block. The minus sign in the source's fourth term is
retained by the dyadic block and disappears only after taking its norm.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 22--23, preceding equation
(6.15). Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- The SEM-455 product-cutoff maximum for one positive fourth-term bilinear
block. The fourth Vaughan term itself is the negative of this block. -/
def vaughanFourthDyadicBlockMaximum
    (U V : ℝ) (x q alpha : ℕ)
    (chi : DirichletCharacter ℂ q) : ℝ :=
  let M := 2 ^ alpha
  let R := x / M
  bilinearProductCutoffMaximum ((M + M) * R) q chi
    (vaughanFourthDyadicMIndices U V x alpha)
    (vaughanFourthDyadicKIndices V x alpha)
    (fun m ↦ ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
    (fun k ↦ ((vaughanFourthCoefficient V k : ℝ) : ℂ))

/-- Maximum fourth Vaughan term over positive natural endpoints through `x`,
totalized to zero when the endpoint interval is empty. -/
def vaughanTwistedSumFourEndpointMaximum
    (U V : ℝ) (x q : ℕ)
    (chi : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun y ↦ ‖vaughanTwistedSumFour U V y q chi‖)
  else 0

private theorem dyadic_productCap_covers_endpoint
    {x alpha : ℕ} (hMlt : 2 ^ alpha < x) :
    x ≤ ((2 ^ alpha + 2 ^ alpha) * (x / 2 ^ alpha)) := by
  let M : ℕ := 2 ^ alpha
  have hMpos : 0 < M := by positivity
  have hRpos : 0 < x / M := Nat.div_pos hMlt.le hMpos
  have hMle : M ≤ M * (x / M) := by
    simpa using Nat.mul_le_mul_left M hRpos
  have hxlt : x < M + M * (x / M) := by
    calc
      x = x % M + M * (x / M) := (Nat.mod_add_div x M).symm
      _ < M + M * (x / M) :=
        Nat.add_lt_add_right (Nat.mod_lt x hMpos) _
  change x ≤ (M + M) * (x / M)
  calc
    x ≤ M + M * (x / M) := hxlt.le
    _ ≤ M * (x / M) + M * (x / M) :=
      Nat.add_le_add_right hMle _
    _ = (M + M) * (x / M) := (Nat.add_mul M M _).symm

private theorem norm_vaughanTwistedSumFourDyadicBlock_le_maximum
    {U V : ℝ} {x y q alpha : ℕ}
    (hV : 1 ≤ V)
    (halpha : alpha ∈ vaughanFourthDyadicExponents U V x)
    (hy : y ∈ Finset.Icc 1 x)
    (chi : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumFourDyadicBlock U V x y q alpha chi‖ ≤
      vaughanFourthDyadicBlockMaximum U V x q alpha chi := by
  have hMltReal : ((2 ^ alpha : ℕ) : ℝ) < (x : ℝ) := by
    rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
    dsimp only at halphaBounds
    have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
    calc
      ((2 ^ alpha : ℕ) : ℝ) < (x : ℝ) / V := halphaBounds.2
      _ ≤ (x : ℝ) := by
        rw [div_le_iff₀ hVpos]
        nlinarith
  have hMlt : 2 ^ alpha < x := by exact_mod_cast hMltReal
  have hyCap : y ∈
      Finset.Icc 1 ((2 ^ alpha + 2 ^ alpha) * (x / 2 ^ alpha)) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hy).1,
      (Finset.mem_Icc.mp hy).2.trans
        (dyadic_productCap_covers_endpoint hMlt)⟩
  simpa only [vaughanTwistedSumFourDyadicBlock,
      vaughanFourthDyadicBlockMaximum, norm_neg] using
    norm_bilinearProductCutoffSum_le_maximum
      ((2 ^ alpha + 2 ^ alpha) * (x / 2 ^ alpha)) q chi
      (vaughanFourthDyadicMIndices U V x alpha)
      (vaughanFourthDyadicKIndices V x alpha)
      (fun m ↦ ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
      (fun k ↦ ((vaughanFourthCoefficient V k : ℝ) : ℂ)) hyCap

/-- The endpoint maximum is bounded by the sum of the separate positive
bilinear block maxima. -/
theorem vaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {x q : ℕ} (hx : 1 ≤ x)
    (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumFourEndpointMaximum U V x q chi ≤
      ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        vaughanFourthDyadicBlockMaximum U V x q alpha chi := by
  rw [vaughanTwistedSumFourEndpointMaximum, dif_pos hx]
  apply Finset.sup'_le
  intro y hy
  rw [vaughanTwistedSumFour_eq_sum_dyadicBlocks
    hU hV (Finset.mem_Icc.mp hy).2 chi]
  calc
    ‖∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        vaughanTwistedSumFourDyadicBlock U V x y q alpha chi‖ ≤
        ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
          ‖vaughanTwistedSumFourDyadicBlock U V x y q alpha chi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        vaughanFourthDyadicBlockMaximum U V x q alpha chi := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact norm_vaughanTwistedSumFourDyadicBlock_le_maximum
        hV halpha hy chi

/-- Weighted primitive-character form of the exact per-block SEM-455 energy
bound, retaining both actual sparse coefficient energies. -/
theorem sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_dyadicEnergy
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
      ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        let M := 2 ^ alpha
        let R := x / M
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
            ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) *
          Real.sqrt (∑ k ∈ vaughanFourthDyadicKIndices V x alpha,
            ‖((vaughanFourthCoefficient V k : ℝ) : ℂ)‖ ^ 2) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
  classical
  let scales := vaughanFourthDyadicExponents U V x
  let weight : ℕ → ℝ := fun q ↦ (q : ℝ) / (q.totient : ℝ)
  have hendpoint :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
    apply Finset.sum_le_sum
    intro q _hq
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro chi _hchi
      exact
        vaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
          hU hV hx chi.1
    · dsimp only [weight]
      positivity
  have hreorder :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi.1) =
        ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
    have hperq (q : ℕ) :
        weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 =
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1) =
          ∑ q ∈ Finset.Ioc 0 Q,
            ∑ alpha ∈ scales,
              weight q * ∑ chi : primitiveCharacters q,
                vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hperq q
      _ = ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 :=
        Finset.sum_comm
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
      simpa only [weight] using hendpoint
    _ = ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := hreorder
    _ ≤ ∑ alpha ∈ scales,
        let M := 2 ^ alpha
        let R := x / M
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
            ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) *
          Real.sqrt (∑ k ∈ vaughanFourthDyadicKIndices V x alpha,
            ‖((vaughanFourthCoefficient V k : ℝ) : ℂ)‖ ^ 2) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro alpha halpha
      let M : ℕ := 2 ^ alpha
      let R : ℕ := x / M
      have hM : 0 < M := by positivity
      have hMltReal : (M : ℝ) < (x : ℝ) := by
        rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
        dsimp only [M] at halphaBounds
        have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
        calc
          (M : ℝ) < (x : ℝ) / V := halphaBounds.2
          _ ≤ (x : ℝ) := by
            rw [div_le_iff₀ hVpos]
            nlinarith [show (0 : ℝ) ≤ x by positivity]
      have hMlt : M < x := by exact_mod_cast hMltReal
      have hR : 0 < R := Nat.div_pos hMlt.le hM
      have hsm : vaughanFourthDyadicMIndices U V x alpha ⊆
          Finset.Ioc M (M + M) := by
        intro m hm
        have hmBlock := (Finset.mem_filter.mp hm).1
        rw [dyadicBlock, Finset.mem_Ioc] at hmBlock
        rw [Finset.mem_Ioc]
        constructor
        · simpa only [M] using hmBlock.1
        · calc
            m ≤ 2 ^ (alpha + 1) := hmBlock.2
            _ = M + M := by
              rw [pow_succ]
              dsimp only [M]
              omega
      have hsn : vaughanFourthDyadicKIndices V x alpha ⊆
          Finset.Ioc 0 (0 + R) := by
        intro k hk
        have hkIoc := (Finset.mem_filter.mp hk).1
        rw [Finset.mem_Ioc] at hkIoc
        rw [Finset.mem_Ioc]
        constructor
        · exact hkIoc.1
        · simpa only [R, M, zero_add] using hkIoc.2
      have hblock :=
        sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
          Q M M 0 R hM hR
          (vaughanFourthDyadicMIndices U V x alpha)
          (vaughanFourthDyadicKIndices V x alpha)
          hsm hsn
          (fun m ↦ ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
          (fun k ↦ ((vaughanFourthCoefficient V k : ℝ) : ℂ))
      simpa only [weight, vaughanFourthDyadicBlockMaximum,
        M, R, zero_add] using hblock
    _ = _ := by rfl

end

end BoundedGaps.Maynard
