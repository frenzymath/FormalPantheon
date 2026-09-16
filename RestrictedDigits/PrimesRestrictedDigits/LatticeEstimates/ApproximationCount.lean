import PrimesRestrictedDigits.BasicEstimates.DivisorSubpolynomial
import PrimesRestrictedDigits.LatticeEstimates.HybridSums
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.ModEq

/-!
# Approximation counts in the lattice estimate

This file defines the literal `N(a,d)` carrier from published Lemma 14.3 and proves its
repaired determinant count.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Denominators counted by `N(a,d)`. The source deliberately enlarges the
preceding carrier: `q` is not required to be coprime to ten, and the natural
numerator witness has no range restriction. -/
noncomputable def latticeApproximationDenominators
    (length : Nat) (a : Fin (10 ^ length)) (d Q G E : Nat) : Finset Nat := by
  classical
  exact (latticeFactorTenBand Q).filter fun q =>
    ∃ b g : Nat,
      g ∈ latticeFactorTenBand G ∧
      b.Coprime (d * q * g) ∧
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
          (b : Real) / ((d * q * g : Nat) : Real)| <=
        (E : Real) / ((10 ^ length : Nat) : Real)

/-- The natural cardinality denoted by `N(a,d)` in Lemma 14.3. -/
def latticeApproximationCount
    (length : Nat) (a : Fin (10 ^ length)) (d Q G E : Nat) : Nat :=
  (latticeApproximationDenominators length a d Q G E).card

theorem mem_latticeApproximationDenominators_iff
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E q : Nat} :
    q ∈ latticeApproximationDenominators length a d Q G E <->
      q ∈ latticeFactorTenBand Q ∧
      ∃ b g : Nat,
        g ∈ latticeFactorTenBand G ∧
        b.Coprime (d * q * g) ∧
        |(a.val : Real) / ((10 ^ length : Nat) : Real) -
            (b : Real) / ((d * q * g : Nat) : Real)| <=
          (E : Real) / ((10 ^ length : Nat) : Real) := by
  simp [latticeApproximationDenominators]

private theorem exists_latticeApproximationWitnessPair
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    ∃ w : Nat × Nat,
      w.2 ∈ latticeFactorTenBand G ∧
      w.1.Coprime (d * q.val * w.2) ∧
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
          (w.1 : Real) / ((d * q.val * w.2 : Nat) : Real)| <=
        (E : Real) / ((10 ^ length : Nat) : Real) := by
  rcases (mem_latticeApproximationDenominators_iff.mp q.property).2 with
    ⟨b, g, hg, hcop, happ⟩
  exact ⟨(b, g), hg, hcop, happ⟩

private noncomputable def latticeApproximationWitness
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    Nat × Nat :=
  Classical.choose (exists_latticeApproximationWitnessPair q)

private theorem latticeApproximationWitness_spec
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    let w := latticeApproximationWitness q
    w.2 ∈ latticeFactorTenBand G ∧
      w.1.Coprime (d * q.val * w.2) ∧
      |(a.val : Real) / ((10 ^ length : Nat) : Real) -
          (w.1 : Real) / ((d * q.val * w.2 : Nat) : Real)| <=
        (E : Real) / ((10 ^ length : Nat) : Real) :=
  Classical.choose_spec (exists_latticeApproximationWitnessPair q)

private def latticeApproximationProduct
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) : Nat :=
  q.val * (latticeApproximationWitness q).2

private theorem latticeApproximationProduct_pos
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    0 < latticeApproximationProduct q := by
  have hq := (mem_latticeApproximationDenominators_iff.mp q.property).1
  have hqPos := (mem_latticeFactorTenBand_iff.mp hq).1
  have hg := (latticeApproximationWitness_spec q).1
  have hgPos := (mem_latticeFactorTenBand_iff.mp hg).1
  exact Nat.mul_pos hqPos hgPos

private theorem latticeApproximationProduct_le
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    latticeApproximationProduct q <= Q * G := by
  have hq := (mem_latticeApproximationDenominators_iff.mp q.property).1
  have hqUpper := (mem_latticeFactorTenBand_iff.mp hq).2.1
  have hg := (latticeApproximationWitness_spec q).1
  have hgUpper := (mem_latticeFactorTenBand_iff.mp hg).2.1
  exact Nat.mul_le_mul hqUpper hgUpper

private theorem latticeApproximationScale_lt_hundred_mul
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (q : {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    Q * G < 100 * latticeApproximationProduct q := by
  have hq := (mem_latticeApproximationDenominators_iff.mp q.property).1
  have hqLower := (mem_latticeFactorTenBand_iff.mp hq).2.2
  have hg := (latticeApproximationWitness_spec q).1
  have hgData := mem_latticeFactorTenBand_iff.mp hg
  have hgLower := hgData.2.2
  have hGPos : 0 < G :=
    (lt_of_lt_of_le Nat.zero_lt_one hgData.1).trans_le hgData.2.1
  have hfirst : Q * G < (10 * q.val) * G :=
    Nat.mul_lt_mul_of_pos_right hqLower hGPos
  have hsecond : (10 * q.val) * G < (10 * q.val) * (10 *
      (latticeApproximationWitness q).2) :=
    Nat.mul_lt_mul_of_pos_left hgLower
      (Nat.mul_pos (by norm_num)
        (mem_latticeFactorTenBand_iff.mp hq).1)
  calc
    Q * G < (10 * q.val) * (10 *
        (latticeApproximationWitness q).2) := hfirst.trans hsecond
    _ = 100 * latticeApproximationProduct q := by
      unfold latticeApproximationProduct
      ring

private def latticeApproximationDeterminant
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (anchor q :
      {q // q ∈ latticeApproximationDenominators length a d Q G E}) : Int :=
  ((latticeApproximationWitness anchor).1 : Int) *
      (latticeApproximationProduct q : Int) -
    ((latticeApproximationWitness q).1 : Int) *
      (latticeApproximationProduct anchor : Int)

private theorem latticeApproximationDeterminant_abs_le
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (hd : 0 < d)
    (anchor q :
      {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    |(latticeApproximationDeterminant anchor q : Real)| <=
      2 * (E : Real) * d * Q ^ 2 * G ^ 2 /
        ((10 ^ length : Nat) : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let m0 : Nat := latticeApproximationProduct anchor
  let m : Nat := latticeApproximationProduct q
  let b0 : Nat := (latticeApproximationWitness anchor).1
  let b : Nat := (latticeApproximationWitness q).1
  have hX : 0 < X := by positivity
  have hm0 : 0 < m0 := latticeApproximationProduct_pos anchor
  have hm : 0 < m := latticeApproximationProduct_pos q
  have hanchor := (latticeApproximationWitness_spec anchor).2.2
  have hq := (latticeApproximationWitness_spec q).2.2
  have hdiff :
      |(b0 : Real) / ((d * m0 : Nat) : Real) -
          (b : Real) / ((d * m : Nat) : Real)| <= 2 * (E : Real) / X := by
    calc
      |(b0 : Real) / ((d * m0 : Nat) : Real) -
          (b : Real) / ((d * m : Nat) : Real)| =
          |((a.val : Real) / X - (b : Real) / ((d * m : Nat) : Real)) -
            ((a.val : Real) / X -
              (b0 : Real) / ((d * m0 : Nat) : Real))| := by
            congr 1
            ring
      _ <= |(a.val : Real) / X - (b : Real) / ((d * m : Nat) : Real)| +
          |(a.val : Real) / X - (b0 : Real) / ((d * m0 : Nat) : Real)| :=
        abs_sub _ _
      _ <= (E : Real) / X + (E : Real) / X := by
        gcongr
        · simpa only [X, m, b, latticeApproximationProduct,
            Nat.mul_assoc] using hq
        · simpa only [X, m0, b0, latticeApproximationProduct,
            Nat.mul_assoc] using hanchor
      _ = 2 * (E : Real) / X := by ring
  have hidentity :
      |(b0 : Real) * m - (b : Real) * m0| =
        (((d * m0 * m : Nat) : Real)) *
          |(b0 : Real) / ((d * m0 : Nat) : Real) -
            (b : Real) / ((d * m : Nat) : Real)| := by
    calc
      |(b0 : Real) * m - (b : Real) * m0| =
          |(((d * m0 * m : Nat) : Real)) *
            ((b0 : Real) / ((d * m0 : Nat) : Real) -
              (b : Real) / ((d * m : Nat) : Real))| := by
            congr 1
            norm_num only [Nat.cast_mul]
            field_simp [hd.ne', hm0.ne', hm.ne']
      _ = |(((d * m0 * m : Nat) : Real))| *
          |(b0 : Real) / ((d * m0 : Nat) : Real) -
            (b : Real) / ((d * m : Nat) : Real)| := abs_mul _ _
      _ = (((d * m0 * m : Nat) : Real)) *
          |(b0 : Real) / ((d * m0 : Nat) : Real) -
            (b : Real) / ((d * m : Nat) : Real)| := by
        rw [abs_of_nonneg]
        positivity
  have hm0Upper : m0 <= Q * G := latticeApproximationProduct_le anchor
  have hmUpper : m <= Q * G := latticeApproximationProduct_le q
  have hdetCast : (latticeApproximationDeterminant anchor q : Real) =
      (b0 : Real) * m - (b : Real) * m0 := by
    simp only [latticeApproximationDeterminant, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast]
    rfl
  rw [hdetCast]
  calc
    |(b0 : Real) * m - (b : Real) * m0| =
        (((d * m0 * m : Nat) : Real)) *
          |(b0 : Real) / ((d * m0 : Nat) : Real) -
            (b : Real) / ((d * m : Nat) : Real)| := hidentity
    _ <= (((d * m0 * m : Nat) : Real)) * (2 * (E : Real) / X) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ <= 2 * (E : Real) * d * Q ^ 2 * G ^ 2 / X := by
      norm_num only [Nat.cast_mul, Nat.cast_pow]
      have hm0Real : (m0 : Real) <= Q * G := by exact_mod_cast hm0Upper
      have hmReal : (m : Real) <= Q * G := by exact_mod_cast hmUpper
      have hprod : (m0 : Real) * m <= ((Q : Real) * G) ^ 2 := by
        calc
          (m0 : Real) * m <= ((Q : Real) * G) * (Q * G) :=
            mul_le_mul hm0Real hmReal (by positivity) (by positivity)
          _ = ((Q : Real) * G) ^ 2 := by ring
      calc
        (d : Real) * m0 * m * (2 * E / X) =
            (2 * E * d / X) * (m0 * m) := by ring
        _ <= (2 * E * d / X) * (((Q : Real) * G) ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 * E * d * Q ^ 2 * G ^ 2 / X := by ring

private def latticeApproximationKey
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (anchor q :
      {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    Int × Nat :=
  (latticeApproximationDeterminant anchor q,
    latticeApproximationProduct q / latticeApproximationProduct anchor)

private theorem latticeApproximationProduct_eq_of_key_eq
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (anchor q₁ q₂ :
      {q // q ∈ latticeApproximationDenominators length a d Q G E})
    (hkey : latticeApproximationKey anchor q₁ =
      latticeApproximationKey anchor q₂) :
    latticeApproximationProduct q₁ = latticeApproximationProduct q₂ := by
  let b₀ : Nat := (latticeApproximationWitness anchor).1
  let b₁ : Nat := (latticeApproximationWitness q₁).1
  let b₂ : Nat := (latticeApproximationWitness q₂).1
  let m₀ : Nat := latticeApproximationProduct anchor
  let m₁ : Nat := latticeApproximationProduct q₁
  let m₂ : Nat := latticeApproximationProduct q₂
  have hdet := congrArg Prod.fst hkey
  have hquot := congrArg Prod.snd hkey
  change latticeApproximationDeterminant anchor q₁ =
    latticeApproximationDeterminant anchor q₂ at hdet
  change m₁ / m₀ = m₂ / m₀ at hquot
  have hcrossInt :
      (b₀ : Int) * m₁ + (b₂ : Int) * m₀ =
        (b₀ : Int) * m₂ + (b₁ : Int) * m₀ := by
    change (b₀ : Int) * m₁ - (b₁ : Int) * m₀ =
      (b₀ : Int) * m₂ - (b₂ : Int) * m₀ at hdet
    linear_combination hdet
  have hcrossNat : b₀ * m₁ + b₂ * m₀ = b₀ * m₂ + b₁ * m₀ := by
    exact_mod_cast hcrossInt
  have hmulMod : b₀ * m₁ ≡ b₀ * m₂ [MOD m₀] := by
    rw [Nat.ModEq]
    have hrem := congrArg (fun n : Nat => n % m₀) hcrossNat
    simpa [Nat.add_mod] using hrem
  have hcopFull := (latticeApproximationWitness_spec anchor).2.1
  have hm₀Dvd : m₀ ∣ d * anchor.val *
      (latticeApproximationWitness anchor).2 := by
    refine ⟨d, ?_⟩
    dsimp only [m₀, latticeApproximationProduct]
    ring
  have hcop : b₀.Coprime m₀ := by
    exact Nat.Coprime.of_dvd_right hm₀Dvd hcopFull
  have hproductMod : m₁ ≡ m₂ [MOD m₀] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one hmulMod
  exact Nat.ext_div_modEq hquot hproductMod

private theorem latticeApproximationKey_mem
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (hd : 0 < d)
    (anchor q :
      {q // q ∈ latticeApproximationDenominators length a d Q G E}) :
    latticeApproximationKey anchor q ∈
      Finset.Icc
          (-(Nat.ceil (2 * (E : Real) * d * Q ^ 2 * G ^ 2 /
            ((10 ^ length : Nat) : Real)) : Int))
          (Nat.ceil (2 * (E : Real) * d * Q ^ 2 * G ^ 2 /
            ((10 ^ length : Nat) : Real)) : Int) ×ˢ
        Finset.range 100 := by
  have hdet := latticeApproximationDeterminant_abs_le hd anchor q
  let R : Real := 2 * (E : Real) * d * Q ^ 2 * G ^ 2 /
    ((10 ^ length : Nat) : Real)
  let H : Nat := Nat.ceil R
  have hR : 0 <= R := by positivity
  have hceil : R <= (H : Real) := Nat.le_ceil R
  have hdetR : |(latticeApproximationDeterminant anchor q : Real)| <= R := by
    simpa only [R] using hdet
  have habs : |(latticeApproximationDeterminant anchor q : Real)| <=
      (H : Real) := hdetR.trans hceil
  have hboundsReal := abs_le.mp habs
  have hboundsInt :
      -(H : Int) <= latticeApproximationDeterminant anchor q ∧
        latticeApproximationDeterminant anchor q <= (H : Int) := by
    constructor
    · exact_mod_cast hboundsReal.1
    · exact_mod_cast hboundsReal.2
  have hproduct : latticeApproximationProduct q <
      100 * latticeApproximationProduct anchor :=
    (latticeApproximationProduct_le q).trans_lt
      (latticeApproximationScale_lt_hundred_mul anchor)
  have hquotient : latticeApproximationProduct q /
      latticeApproximationProduct anchor < 100 :=
    (Nat.div_lt_iff_lt_mul
      (latticeApproximationProduct_pos anchor)).2 hproduct
  simpa only [latticeApproximationKey, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range, R, H] using And.intro hboundsInt hquotient

private theorem card_latticeApproximationKeySpace_le
    (length d Q G E : Nat) :
    let T : Real := ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
      ((10 ^ length : Nat) : Real)
    let H : Nat := Nat.ceil (2 * T)
    (((Finset.Icc (-(H : Int)) (H : Int) ×ˢ Finset.range 100).card : Nat) :
        Real) <= 400 * (1 + T) := by
  let T : Real := ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
    ((10 ^ length : Nat) : Real)
  let H : Nat := Nat.ceil (2 * T)
  have hT : 0 <= T := by positivity
  have hH : (H : Real) < 2 * T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hintervalInt :
      (((Finset.Icc (-(H : Int)) (H : Int)).card : Nat) : Int) =
        2 * (H : Int) + 1 := by
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  have hintervalNat :
      (Finset.Icc (-(H : Int)) (H : Int)).card = 2 * H + 1 := by
    exact_mod_cast hintervalInt
  change (((Finset.Icc (-(H : Int)) (H : Int) ×ˢ
      Finset.range 100).card : Nat) : Real) <= 400 * (1 + T)
  rw [Finset.card_product, hintervalNat, Finset.card_range]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  change ((2 * (H : Real) + 1) * 100) <= 400 * (1 + T)
  nlinarith

private theorem latticeApproximationKeyFiber_card_le
    {length : Nat} {a : Fin (10 ^ length)} {d Q G E : Nat}
    (rho C : Real) (hrho : 0 < rho)
    (hdiv : ∀ n : Nat, (n.divisors.card : Real) <= C * (n : Real) ^ rho)
    (anchor :
      {q // q ∈ latticeApproximationDenominators length a d Q G E})
    (key : Int × Nat) :
    (((Finset.univ.filter fun q => latticeApproximationKey anchor q = key).card :
        Nat) : Real) <= C * (((Q * G : Nat) : Real) ^ rho) := by
  classical
  let fiber : Finset
      {q // q ∈ latticeApproximationDenominators length a d Q G E} :=
    (Finset.univ.filter fun q =>
    latticeApproximationKey anchor q = key)
  have hC : 0 <= C := by
    have hone := hdiv 1
    norm_num at hone
    linarith
  by_cases hfiber : fiber.Nonempty
  · let representative := hfiber.choose
    have hrepresentative : representative ∈ fiber := hfiber.choose_spec
    let target := (latticeApproximationProduct representative).divisors
    have hmaps : Set.MapsTo
        (fun q : {q // q ∈ latticeApproximationDenominators length a d Q G E} =>
          q.val) (fiber : Set _) (target : Set Nat) := by
      intro q hq
      have hqKey := (Finset.mem_filter.mp hq).2
      have hrepKey := (Finset.mem_filter.mp hrepresentative).2
      have hproduct := latticeApproximationProduct_eq_of_key_eq
        anchor q representative (hqKey.trans hrepKey.symm)
      apply Nat.mem_divisors.mpr
      constructor
      · refine ⟨(latticeApproximationWitness q).2, ?_⟩
        rw [← hproduct]
        rfl
      · exact (latticeApproximationProduct_pos representative).ne'
    have hinj : Set.InjOn
        (fun q : {q // q ∈ latticeApproximationDenominators length a d Q G E} =>
          q.val) (fiber : Set _) :=
      Set.injOn_of_injective Subtype.val_injective
    have hcardNat : fiber.card <= target.card :=
      Finset.card_le_card_of_injOn Subtype.val hmaps hinj
    have hcardReal : (fiber.card : Real) <= (target.card : Real) := by
      exact_mod_cast hcardNat
    have hpower : (latticeApproximationProduct representative : Real) ^ rho <=
        ((Q * G : Nat) : Real) ^ rho :=
      Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast latticeApproximationProduct_le representative)
        hrho.le
    calc
      (fiber.card : Real) <= (target.card : Real) := hcardReal
      _ <= C * (latticeApproximationProduct representative : Real) ^ rho :=
        hdiv _
      _ <= C * ((Q * G : Nat) : Real) ^ rho := by
        exact mul_le_mul_of_nonneg_left hpower hC
  · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
    rw [show (Finset.univ.filter fun q =>
      latticeApproximationKey anchor q = key) = fiber from rfl, hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg (Q * G)) rho)

/-- The repaired uniform estimate for `N(a,d)`. The two absolute counting
losses are absorbed into a constant depending only on `rho`. -/
theorem exists_latticeApproximationCount_le (rho : Real) (hrho : 0 < rho) :
    ∃ C : Real, 0 < C ∧
      ∀ (length : Nat) (a : Fin (10 ^ length)) (d Q G E : Nat),
        0 < d -> 0 < Q -> 0 < G ->
        (latticeApproximationCount length a d Q G E : Real) <=
          C * (((Q * G : Nat) : Real) ^ rho) *
            (1 + ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
              ((10 ^ length : Nat) : Real)) := by
  obtain ⟨Cdiv, hCdiv, hdiv⟩ :=
    card_divisors_le_const_mul_rpow rho hrho
  refine ⟨400 * Cdiv, mul_pos (by norm_num) hCdiv, ?_⟩
  intro length a d Q G E hd hQ hG
  classical
  let s := latticeApproximationDenominators length a d Q G E
  by_cases hs : s.Nonempty
  · let anchor : {q // q ∈ latticeApproximationDenominators length a d Q G E} :=
      ⟨hs.choose, by simpa only [s] using hs.choose_spec⟩
    let T : Real := ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
      ((10 ^ length : Nat) : Real)
    let H : Nat := Nat.ceil (2 * T)
    let keySpace := Finset.Icc (-(H : Int)) (H : Int) ×ˢ Finset.range 100
    have hradius :
        2 * (E : Real) * d * Q ^ 2 * G ^ 2 /
            ((10 ^ length : Nat) : Real) = 2 * T := by
      dsimp only [T]
      norm_num only [Nat.cast_mul, Nat.cast_pow]
      ring
    have hmaps : Set.MapsTo (latticeApproximationKey anchor)
        ((Finset.univ : Finset
          {q // q ∈ latticeApproximationDenominators length a d Q G E}) : Set _)
        (keySpace : Set (Int × Nat)) := by
      intro q hq
      have hmem := latticeApproximationKey_mem hd anchor q
      rw [hradius] at hmem
      change latticeApproximationKey anchor q ∈ keySpace
      simpa only [keySpace, H] using hmem
    have hcardFibers := Finset.card_eq_sum_card_fiberwise hmaps
    have hkeyCard : (keySpace.card : Real) <= 400 * (1 + T) := by
      simpa only [keySpace, H, T] using
        card_latticeApproximationKeySpace_le length d Q G E
    have hCdivNonneg : 0 <= Cdiv := hCdiv.le
    calc
      (latticeApproximationCount length a d Q G E : Real) =
          ((Finset.univ : Finset
            {q // q ∈ latticeApproximationDenominators length a d Q G E}).card :
              Real) := by
        simp [latticeApproximationCount]
      _ = ∑ key ∈ keySpace,
          (((Finset.univ.filter fun q =>
            latticeApproximationKey anchor q = key).card : Nat) : Real) := by
        exact_mod_cast hcardFibers
      _ <= ∑ _key ∈ keySpace,
          Cdiv * (((Q * G : Nat) : Real) ^ rho) := by
        apply Finset.sum_le_sum
        intro key hkey
        exact latticeApproximationKeyFiber_card_le
          rho Cdiv hrho hdiv anchor key
      _ = (keySpace.card : Real) *
          (Cdiv * (((Q * G : Nat) : Real) ^ rho)) := by
        simp
      _ <= (400 * (1 + T)) *
          (Cdiv * (((Q * G : Nat) : Real) ^ rho)) :=
        mul_le_mul_of_nonneg_right hkeyCard
          (mul_nonneg hCdivNonneg (Real.rpow_nonneg (by positivity) rho))
      _ = (400 * Cdiv) * (((Q * G : Nat) : Real) ^ rho) *
          (1 + ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
            ((10 ^ length : Nat) : Real)) := by
        dsimp only [T]
        ring
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hcarrier : latticeApproximationDenominators length a d Q G E = ∅ := by
      simpa only [s] using hempty
    rw [latticeApproximationCount, hcarrier]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end

end PrimesRestrictedDigits
