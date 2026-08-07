import BoundedGaps.BombieriVinogradov.Analytic.MaximalBilinearConclusion
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermLargeDyadic

/-!
# Energy bounds for Vaughan's large third term

This file lifts the exact dyadic decomposition of the large third Vaughan term
to per-character endpoint maxima, applies the sparse maximal bilinear large
sieve on every active block, and bounds the resulting third-coefficient
energies.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 21--22, preceding equation
(6.13). Semantic review: `SEM-456`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- The SEM-455 product-cutoff maximum for one active dyadic block. -/
def vaughanThirdLargeDyadicBlockMaximum
    (U V : ℝ) (x q alpha : ℕ)
    (chi : DirichletCharacter ℂ q) : ℝ :=
  let M := 2 ^ alpha
  let R := x / M
  bilinearProductCutoffMaximum ((M + M) * R) q chi
    (vaughanThirdLargeDyadicIndices U V x alpha)
    (vaughanThirdLargeDyadicRIndices x alpha)
    (fun t ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
    (fun _ ↦ 1)

/-- Maximum large third Vaughan term over positive natural endpoints through
`x`, totalized to zero when the endpoint interval is empty. -/
def vaughanTwistedSumThreeLargeEndpointMaximum
    (U V : ℝ) (x q : ℕ)
    (chi : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun y ↦ ‖vaughanTwistedSumThreeLarge U V y q chi‖)
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

private theorem norm_vaughanTwistedSumThreeLargeDyadicBlock_le_maximum
    {U V : ℝ} {x y q alpha : ℕ}
    (halpha : alpha ∈ vaughanThirdLargeDyadicExponents U V x)
    (hy : y ∈ Finset.Icc 1 x)
    (chi : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi‖ ≤
      vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi := by
  have hMlt : 2 ^ alpha < x := by
    rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
    dsimp only at halphaBounds
    exact halphaBounds.2.2
  have hyCap : y ∈
      Finset.Icc 1 ((2 ^ alpha + 2 ^ alpha) * (x / 2 ^ alpha)) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hy).1,
      (Finset.mem_Icc.mp hy).2.trans
        (dyadic_productCap_covers_endpoint hMlt)⟩
  simpa only [vaughanTwistedSumThreeLargeDyadicBlock,
      vaughanThirdLargeDyadicBlockMaximum] using
    norm_bilinearProductCutoffSum_le_maximum
      ((2 ^ alpha + 2 ^ alpha) * (x / 2 ^ alpha)) q chi
      (vaughanThirdLargeDyadicIndices U V x alpha)
      (vaughanThirdLargeDyadicRIndices x alpha)
      (fun t ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
      (fun _ ↦ (1 : ℂ)) hyCap

/-- The endpoint maximum is bounded by the sum of the separate dyadic block
maxima; the maximizing endpoint remains character-dependent. -/
theorem vaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {x q : ℕ} (hx : 1 ≤ x)
    (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi ≤
      ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi := by
  rw [vaughanTwistedSumThreeLargeEndpointMaximum, dif_pos hx]
  apply Finset.sup'_le
  intro y hy
  rw [vaughanTwistedSumThreeLarge_eq_sum_dyadicBlocks
    hU hV (Finset.mem_Icc.mp hy).2 chi]
  calc
    ‖∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi‖ ≤
        ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
          ‖vaughanTwistedSumThreeLargeDyadicBlock U V x y q alpha chi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact norm_vaughanTwistedSumThreeLargeDyadicBlock_le_maximum
        halpha hy chi

/-- Weighted primitive-character form of the exact per-block SEM-455 energy
bound. -/
theorem sum_weightedPrimitiveVaughanTwistedSumThreeLargeEndpointMaximum_le_dyadicEnergy
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
      ∑ alpha ∈ vaughanThirdLargeDyadicExponents U V x,
        let M := 2 ^ alpha
        let R := x / M
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
            ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) *
          Real.sqrt (R : ℝ) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
  classical
  let scales := vaughanThirdLargeDyadicExponents U V x
  let weight : ℕ → ℝ := fun q ↦ (q : ℝ) / (q.totient : ℝ)
  have hendpoint :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
    apply Finset.sum_le_sum
    intro q _hq
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro chi _hchi
      exact
        vaughanTwistedSumThreeLargeEndpointMaximum_le_sum_dyadicBlockMaximum
          hU hV hx chi.1
    · dsimp only [weight]
      positivity
  have hreorder :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1) =
        ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
    have hperq (q : ℕ) :
        weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 =
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1) =
          ∑ q ∈ Finset.Ioc 0 Q,
            ∑ alpha ∈ scales,
              weight q * ∑ chi : primitiveCharacters q,
                vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hperq q
      _ = ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 :=
        Finset.sum_comm
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumThreeLargeEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := by
      simpa only [weight] using hendpoint
    _ =
        ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanThirdLargeDyadicBlockMaximum U V x q alpha chi.1 := hreorder
    _ ≤ ∑ alpha ∈ scales,
        let M := 2 ^ alpha
        let R := x / M
        akbaryHambrookC3 *
          Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt ((R : ℝ) + (Q : ℝ) ^ 2) *
          Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
            ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) *
          Real.sqrt (R : ℝ) *
          Real.log (2 * (((M + M) * R : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro alpha halpha
      let M : ℕ := 2 ^ alpha
      let R : ℕ := x / M
      have hM : 0 < M := by positivity
      have hMlt : M < x := by
        rcases Finset.mem_filter.mp halpha with ⟨_halphaRange, halphaBounds⟩
        dsimp only [M] at halphaBounds
        exact halphaBounds.2.2
      have hR : 0 < R := Nat.div_pos hMlt.le hM
      have hsm : vaughanThirdLargeDyadicIndices U V x alpha ⊆
          Finset.Ioc M (M + M) := by
        intro t ht
        have htBlock := (Finset.mem_inter.mp ht).2
        rw [dyadicBlock, Finset.mem_Ioc] at htBlock
        rw [Finset.mem_Ioc]
        constructor
        · simpa only [M] using htBlock.1
        · calc
            t ≤ 2 ^ (alpha + 1) := htBlock.2
            _ = M + M := by
              rw [pow_succ]
              dsimp only [M]
              omega
      have hsn : vaughanThirdLargeDyadicRIndices x alpha ⊆
          Finset.Ioc 0 (0 + R) := by
        intro r hr
        rw [vaughanThirdLargeDyadicRIndices, Finset.mem_Icc] at hr
        rw [Finset.mem_Ioc]
        constructor
        · omega
        · simpa only [R, M, zero_add] using hr.2
      have hblock :=
        sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
          Q M M 0 R hM hR
          (vaughanThirdLargeDyadicIndices U V x alpha)
          (vaughanThirdLargeDyadicRIndices x alpha)
          hsm hsn
          (fun t ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
          (fun _ ↦ (1 : ℂ))
      have hcardR : (vaughanThirdLargeDyadicRIndices x alpha).card = R := by
        rw [vaughanThirdLargeDyadicRIndices, Nat.card_Icc]
        simp [R, M]
      simpa only [weight, vaughanThirdLargeDyadicBlockMaximum,
        M, R, zero_add, norm_one, one_pow, Finset.sum_const, hcardR,
        Nat.cast_id, nsmul_eq_mul, mul_one] using hblock
    _ = _ := by rfl

/-- The actual third-coefficient square energy on one dyadic block is bounded
by its ambient span times the squared endpoint logarithm. -/
theorem sum_norm_sq_vaughanThirdCoefficient_dyadic_le
    (U V : ℝ) (x alpha : ℕ) :
    (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
      ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) ≤
      ((2 ^ alpha : ℕ) : ℝ) *
        (Real.log (2 * ((2 ^ alpha : ℕ) : ℝ))) ^ 2 := by
  classical
  let M : ℕ := 2 ^ alpha
  have hMpos : 0 < M := by positivity
  have hlogNonneg : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hcard : (vaughanThirdLargeDyadicIndices U V x alpha).card ≤ M := by
    calc
      (vaughanThirdLargeDyadicIndices U V x alpha).card ≤
          (dyadicBlock alpha).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = M := by
        rw [dyadicBlock, Nat.card_Ioc, pow_succ]
        dsimp only [M]
        omega
  calc
    (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
        ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ _t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
          (Real.log (2 * (M : ℝ))) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have htBlock := (Finset.mem_inter.mp ht).2
      have htBounds := Finset.mem_Ioc.mp (show t ∈ dyadicBlock alpha from htBlock)
      have htpos : 0 < t := hMpos.trans htBounds.1
      have htUpperNat : t ≤ M + M := by
        calc
          t ≤ 2 ^ (alpha + 1) := htBounds.2
          _ = M + M := by
            rw [pow_succ]
            dsimp only [M]
            omega
      have htUpper : (t : ℝ) ≤ 2 * (M : ℝ) := by
        have htUpperNat' : t ≤ 2 * M := by omega
        exact_mod_cast htUpperNat'
      have hnorm : ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ≤
          Real.log (2 * (M : ℝ)) :=
        (norm_vaughanThirdCoefficient_le_log U V t).trans
          (Real.log_le_log (by exact_mod_cast htpos) htUpper)
      exact (sq_le_sq₀ (norm_nonneg _) hlogNonneg).2 hnorm
    _ = ((vaughanThirdLargeDyadicIndices U V x alpha).card : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 := by simp
    _ ≤ (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = ((2 ^ alpha : ℕ) : ℝ) *
        (Real.log (2 * ((2 ^ alpha : ℕ) : ℝ))) ^ 2 := by rfl

/-- Square-root form of the third-coefficient dyadic energy bound. -/
theorem sqrt_sum_norm_sq_vaughanThirdCoefficient_dyadic_le
    (U V : ℝ) (x alpha : ℕ) :
    Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
      ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) ≤
      Real.sqrt ((2 ^ alpha : ℕ) : ℝ) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) := by
  have henergy := sum_norm_sq_vaughanThirdCoefficient_dyadic_le U V x alpha
  have hlogNonneg :
      0 ≤ Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      have hpow : (1 : ℝ) ≤ ((2 ^ alpha : ℕ) : ℝ) := by
        exact_mod_cast (by simpa using Nat.one_le_pow' alpha 1)
      nlinarith)
  calc
    Real.sqrt (∑ t ∈ vaughanThirdLargeDyadicIndices U V x alpha,
        ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ^ 2) ≤
        Real.sqrt (((2 ^ alpha : ℕ) : ℝ) *
          (Real.log (2 * ((2 ^ alpha : ℕ) : ℝ))) ^ 2) :=
      Real.sqrt_le_sqrt henergy
    _ = Real.sqrt ((2 ^ alpha : ℕ) : ℝ) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hlogNonneg]

end

end BoundedGaps.Maynard
