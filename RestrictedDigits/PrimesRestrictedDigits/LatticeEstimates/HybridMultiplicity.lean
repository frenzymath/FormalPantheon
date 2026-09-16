import PrimesRestrictedDigits.BasicEstimates.DivisorSubpolynomial
import PrimesRestrictedDigits.LatticeEstimates.HybridSums

/-!
# Factorized-denominator multiplicity in the lattice estimate

The `S2` sum in published Lemma 14.4 counts multiple pairs `(q', g2)` that can have the same
product. This file inserts the omitted divisor-fiber loss.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- A fixed multiplication fiber in two unrestricted decade bands has at
most one member for each positive divisor of the product. -/
theorem card_latticeFactorTenBand_mul_fiber_le_divisors
    (Q G m : Nat) :
    ((latticeFactorTenBand Q ×ˢ latticeFactorTenBand G).filter
      fun x => x.1 * x.2 = m).card <= m.divisors.card := by
  classical
  let fiber := (latticeFactorTenBand Q ×ˢ latticeFactorTenBand G).filter
    fun x => x.1 * x.2 = m
  change fiber.card <= m.divisors.card
  rcases fiber.eq_empty_or_nonempty with hempty | hnonempty
  · rw [hempty]
    simp
  · let witness := hnonempty.choose
    have hwitness : witness ∈ fiber := hnonempty.choose_spec
    have hwitnessData := Finset.mem_filter.mp hwitness
    have hwitnessProduct : witness.1 * witness.2 = m := hwitnessData.2
    have hwitnessBands := Finset.mem_product.mp hwitnessData.1
    have hwitnessPos : 0 < witness.1 * witness.2 := Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one
        (mem_latticeFactorTenBand_iff.mp hwitnessBands.1).1)
      (lt_of_lt_of_le Nat.zero_lt_one
        (mem_latticeFactorTenBand_iff.mp hwitnessBands.2).1)
    have hmPos : 0 < m := by
      rw [← hwitnessProduct]
      exact hwitnessPos
    have hm : m ≠ 0 := hmPos.ne'
    have hmaps : Set.MapsTo Prod.fst (fiber : Set (Nat × Nat))
        (m.divisors : Set Nat) := by
      intro x hx
      have hxProduct := (Finset.mem_filter.mp hx).2
      apply Nat.mem_divisors.mpr
      exact ⟨⟨x.2, hxProduct.symm⟩, hm⟩
    have hinj : Set.InjOn Prod.fst (fiber : Set (Nat × Nat)) := by
      intro x hx y hy hfirst
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxPos : 0 < x.1 := lt_of_lt_of_le Nat.zero_lt_one
        (mem_latticeFactorTenBand_iff.mp
          (Finset.mem_product.mp hxData.1).1).1
      have hproducts : x.1 * x.2 = y.1 * y.2 :=
        hxData.2.trans hyData.2.symm
      change x.1 = y.1 at hfirst
      have hsecond : x.2 = y.2 := by
        rw [hfirst] at hproducts
        exact Nat.eq_of_mul_eq_mul_left
          (by simpa only [hfirst] using hxPos) hproducts
      exact Prod.ext hfirst hsecond
    exact Finset.card_le_card_of_injOn Prod.fst hmaps hinj

private theorem sum_comp_le_mul_sum_of_card_fiber_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (key : ι -> κ)
    (weight : κ -> Real) (M : Real)
    (hmaps : Set.MapsTo key (s : Set ι) (t : Set κ))
    (hweight : ∀ k, k ∈ t -> 0 <= weight k)
    (hfiber : ∀ k, k ∈ t ->
      ((s.filter fun i => key i = k).card : Real) <= M) :
    (∑ i ∈ s, weight (key i)) <= M * ∑ k ∈ t, weight k := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun i => weight (key i))]
  calc
    (∑ k ∈ t, ∑ i ∈ s with key i = k, weight (key i)) =
        ∑ k ∈ t,
          ((s.filter fun i => key i = k).card : Real) * weight k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ i ∈ s with key i = k, weight (key i)) =
            ∑ _i ∈ s.filter (fun i => key i = k), weight k := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = ((s.filter fun i => key i = k).card : Real) * weight k := by
          simp
    _ <= ∑ k ∈ t, M * weight k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hfiber k hk) (hweight k hk)
    _ = M * ∑ k ∈ t, weight k := by rw [Finset.mul_sum]

private theorem latticeSTwo_fiber_card_le
    {Q G m : Nat} {rho C : Real} (hrho : 0 < rho)
    (hdiv : forall n : Nat,
      (n.divisors.card : Real) <= C * (n : Real) ^ rho) :
    ((((hybridResidualSourceDenominators Q ×ˢ latticeFactorTenBand G).filter
      fun x => x.1 * x.2 = m).card : Nat) : Real) <=
        C * ((Q * G : Nat) : Real) ^ rho := by
  let sourceFiber :=
    (hybridResidualSourceDenominators Q ×ˢ latticeFactorTenBand G).filter
      fun x => x.1 * x.2 = m
  let fullFiber :=
    (latticeFactorTenBand Q ×ˢ latticeFactorTenBand G).filter
      fun x => x.1 * x.2 = m
  change (sourceFiber.card : Real) <=
    C * ((Q * G : Nat) : Real) ^ rho
  have hsubset : sourceFiber ⊆ fullFiber := by
    intro x hx
    have hxData := Finset.mem_filter.mp hx
    have hxBands := Finset.mem_product.mp hxData.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, hxBands.2⟩, hxData.2⟩
    have hq := mem_hybridResidualSourceDenominators_iff.mp hxBands.1
    exact mem_latticeFactorTenBand_iff.mpr ⟨hq.1, hq.2.1, hq.2.2.1⟩
  have hcardNat : sourceFiber.card <= m.divisors.card :=
    (Finset.card_le_card hsubset).trans
      (card_latticeFactorTenBand_mul_fiber_le_divisors Q G m)
  have hcardReal : (sourceFiber.card : Real) <= (m.divisors.card : Real) := by
    exact_mod_cast hcardNat
  have hC : 0 <= C := by
    have hCOne := hdiv 1
    norm_num [Real.one_rpow] at hCOne
    linarith
  by_cases hm : sourceFiber.Nonempty
  · let witness := hm.choose
    have hwitness : witness ∈ sourceFiber := hm.choose_spec
    have hwitnessData := Finset.mem_filter.mp hwitness
    have hwitnessBands := Finset.mem_product.mp hwitnessData.1
    have hmUpper : m <= Q * G := by
      rw [← hwitnessData.2]
      exact Nat.mul_le_mul
        (mem_hybridResidualSourceDenominators_iff.mp
          hwitnessBands.1).2.1
        (mem_latticeFactorTenBand_iff.mp hwitnessBands.2).2.1
    have hpower : (m : Real) ^ rho <= ((Q * G : Nat) : Real) ^ rho :=
      Real.rpow_le_rpow (Nat.cast_nonneg m)
        (by exact_mod_cast hmUpper) hrho.le
    calc
      (sourceFiber.card : Real) <= (m.divisors.card : Real) := hcardReal
      _ <= C * (m : Real) ^ rho := hdiv m
      _ <= C * ((Q * G : Nat) : Real) ^ rho :=
        mul_le_mul_of_nonneg_left hpower hC
  · have hempty : sourceFiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC
      (Real.rpow_nonneg (Nat.cast_nonneg (Q * G)) rho)

/-- The rigorous equation-(14.10) bound. The constant is chosen before every
digit and scale, and the omitted factorization multiplicity is explicit. -/
theorem exists_latticeSTwo_le_hybridBound
    (rho : Real) (hrho : 0 < rho) :
    Exists fun C : Real => And (0 < C)
      (forall (digit : Fin 10) (length d D Q G E : Nat),
        0 < d -> d <= D -> 0 < Q -> 0 < G -> 0 < E ->
        latticeSTwo digit length d Q G E <=
          C * ((Q * G : Nat) : Real) ^ rho *
            latticeHybridTarget length
              (((D * Q ^ 2 * G ^ 2 : Nat) : Real) * E)) := by
  obtain ⟨Cdiv, hCdiv, hdiv⟩ :=
    card_divisors_le_const_mul_rpow rho hrho
  refine ⟨4 * hybridConstant * Cdiv, by
    have hhybrid : 0 < hybridConstant := by norm_num [hybridConstant]
    positivity, ?_⟩
  intro digit length d D Q G E hd hdD hQ hG hE
  let s := hybridResidualSourceDenominators Q ×ˢ latticeFactorTenBand G
  let t := Finset.Icc 1 (Q * G)
  let key : Nat × Nat -> Nat := fun x => x.1 * x.2
  let weight : Nat -> Real := fun m =>
    latticeHybridDenominatorWeight digit length E (d * m)
  let M : Real := Cdiv * ((Q * G : Nat) : Real) ^ rho
  have hmaps : Set.MapsTo key (s : Set (Nat × Nat)) (t : Set Nat) := by
    intro x hx
    have hxBands := Finset.mem_product.mp hx
    have hqData := mem_hybridResidualSourceDenominators_iff.mp hxBands.1
    have hgData := mem_latticeFactorTenBand_iff.mp hxBands.2
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one hqData.1)
      (lt_of_lt_of_le Nat.zero_lt_one hgData.1),
      Nat.mul_le_mul hqData.2.1 hgData.2.1⟩
  have hweight : ∀ m, m ∈ t -> 0 <= weight m := by
    intro m hm
    exact latticeHybridDenominatorWeight_nonneg digit length E (d * m)
  have hfiber : ∀ m, m ∈ t ->
      ((s.filter fun x => key x = m).card : Real) <= M := by
    intro m hm
    exact latticeSTwo_fiber_card_le hrho hdiv
  have hgrouped := sum_comp_le_mul_sum_of_card_fiber_le
    s t key weight M hmaps hweight hfiber
  change latticeSTwo digit length d Q G E <=
    M * latticeHybridMultiplesSum digit length d (Q * G) E at hgrouped
  have hQG : 0 < Q * G := Nat.mul_pos hQ hG
  have hmultiples := latticeHybridMultiplesSum_le_hybridBound
    digit length d (Q * G) E hd hQG hE
  have hM : 0 <= M := by
    dsimp [M]
    positivity
  have hscaleNat : d * (Q * G) ^ 2 <= D * Q ^ 2 * G ^ 2 := by
    calc
      d * (Q * G) ^ 2 <= D * (Q * G) ^ 2 :=
        Nat.mul_le_mul_right _ hdD
      _ = D * Q ^ 2 * G ^ 2 := by ring
  have hscaleReal :
      (((d * (Q * G) ^ 2 : Nat) : Real) * E) <=
        (((D * Q ^ 2 * G ^ 2 : Nat) : Real) * E) :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast hscaleNat) (Nat.cast_nonneg E)
  have htarget := latticeHybridTarget_mono (length := length)
    (by positivity) hscaleReal
  have hhybrid : 0 <= hybridConstant := by norm_num [hybridConstant]
  calc
    latticeSTwo digit length d Q G E <=
        M * latticeHybridMultiplesSum digit length d (Q * G) E := hgrouped
    _ <= M * (4 * hybridConstant *
        latticeHybridTarget length
          (((d * (Q * G) ^ 2 : Nat) : Real) * E)) :=
      mul_le_mul_of_nonneg_left hmultiples hM
    _ <= M * (4 * hybridConstant *
        latticeHybridTarget length
          (((D * Q ^ 2 * G ^ 2 : Nat) : Real) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact mul_le_mul_of_nonneg_left htarget (mul_nonneg (by norm_num) hhybrid)
    _ = (4 * hybridConstant * Cdiv) *
        ((Q * G : Nat) : Real) ^ rho *
          latticeHybridTarget length
            (((D * Q ^ 2 * G ^ 2 : Nat) : Real) * E) := by
      dsimp [M]
      ring

end

end PrimesRestrictedDigits
