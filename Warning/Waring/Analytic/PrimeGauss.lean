import Waring.Analytic.NonfivePrimePower
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Prime-modulus fifth-power sums

This file proves the prime-modulus input for the non-five branches of Chen's
Lemma 2 [CHEN1964-EN, pp. 1547-1548; CHEN1964-ZH, pp. 715-716].
-/

namespace Waring.Analytic

open AddChar MulChar
open scoped BigOperators

/-- If five is coprime to the order of the unit group, fifth powering
permutes the whole prime field. -/
theorem fifthPower_bijective_zmod {p : Nat} (hp : p.Prime)
    (hFifth : (p - 1).Coprime 5) :
    Function.Bijective (fun x : ZMod p => x ^ 5) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  have hUnits : Function.Bijective (fun x : (ZMod p)ˣ => x ^ 5) := by
    apply Nat.Coprime.pow_left_bijective
    rwa [hcard]
  constructor
  · intro x y hxy
    by_cases hx : x = 0
    · subst x
      have hpow : y ^ 5 = 0 := by simpa using hxy.symm
      have hy : y = 0 :=
        (pow_eq_zero_iff (by norm_num : 5 ≠ 0)).mp hpow
      exact hy.symm
    · by_cases hy : y = 0
      · subst y
        have hpow : x ^ 5 = 0 := by simpa using hxy
        have hxZero : x = 0 :=
          (pow_eq_zero_iff (by norm_num : 5 ≠ 0)).mp hpow
        exact (hx hxZero).elim
      · let ux : (ZMod p)ˣ := Units.mk0 x hx
        let uy : (ZMod p)ˣ := Units.mk0 y hy
        have hu : ux ^ 5 = uy ^ 5 := by
          apply Units.ext
          exact hxy
        exact congrArg Units.val (hUnits.1 hu)
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · let uy : (ZMod p)ˣ := Units.mk0 y hy
      obtain ⟨ux, hux⟩ := hUnits.2 uy
      exact ⟨(ux : ZMod p), congrArg Units.val hux⟩

/-- When fifth powering permutes the prime field, the complete sum vanishes. -/
theorem completePowerSum_fifth_prime_eq_zero {p a : Nat} [NeZero p]
    (hp : p.Prime) (hFifth : (p - 1).Coprime 5)
    (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hbij := fifthPower_bijective_zmod hp hFifth
  rw [completePowerSum, powerSum]
  calc
    ∑ x : ZMod p, ZMod.stdAddChar (((a : Nat) : ZMod p) * x ^ 5) =
        ∑ x : ZMod p, ZMod.stdAddChar (((a : Nat) : ZMod p) * x) := by
      exact Equiv.sum_comp (Equiv.ofBijective _ hbij)
        (fun x : ZMod p => ZMod.stdAddChar (((a : Nat) : ZMod p) * x))
    _ = 0 := by
      have haZero : ((a : Nat) : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact hp.coprime_iff_not_dvd.mp ha.symm
      have h := sum_stdAddChar_mul ((a : Nat) : ZMod p)
      rw [if_neg haZero] at h
      norm_num at h
      simpa only [mul_comm] using h

/-- A nontrivial multiplicative Gauss sum against a primitive complex additive
character has norm equal to the square root of the field cardinality. -/
theorem norm_gaussSum_eq_sqrt_card {F : Type*} [Field F] [Fintype F]
    {chi : MulChar F Complex} (hchi : chi ≠ 1)
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) :
    ‖gaussSum chi psi‖ = Real.sqrt (Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hchi hpsi
  rw [← star_gaussSum_eq] at h
  have hn := congrArg norm h
  have hsq : ‖gaussSum chi psi‖ ^ 2 = (Fintype.card F : Real) := by
    simpa [norm_mul, pow_two] using hn
  rw [← Real.sqrt_sq (norm_nonneg _)]
  congr

/-- A fifth-power additive-character sum over a finite field is a sum of four
nontrivial Gauss sums when five divides the unit-group order. -/
theorem fifthPower_sum_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hFive : 5 ∣ Fintype.card F - 1)
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) :
    ‖∑ x : F, psi (x ^ 5)‖ ≤
      4 * Real.sqrt (Fintype.card F) := by
  let fifthHom : Fˣ →* Fˣ := powMonoidHom 5
  let H : Subgroup Fˣ := fifthHom.range
  let X : Subgroup (MulChar F Complex) :=
    (MulChar.subgroupOrderIsoSubgroupMulChar F Complex H).ofDual
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype X := Fintype.ofFinite X
  letI : DecidableEq X := Classical.decEq X
  have hcardUnits : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hcardX : Fintype.card X = 5 := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (MulChar.subgroupOrderIsoSubgroupMulChar F Complex H).ofDual = 5
    rw [MulChar.card_subgroupOrderIsoSubgroupMulChar,
      ← Subgroup.index_eq_card]
    change H.index = 5
    dsimp [H, fifthHom]
    rw [IsCyclic.index_powMonoidHom_range, hcardUnits]
    exact Nat.gcd_eq_right_iff_dvd.mpr hFive
  have hcardKer : Fintype.card fifthHom.ker = 5 := by
    rw [Fintype.card_eq_nat_card]
    dsimp [fifthHom]
    rw [IsCyclic.card_powMonoidHom_ker, hcardUnits]
    exact Nat.gcd_eq_right_iff_dvd.mpr hFive
  have hfiber (b : Fˣ)
      (hb : b ∈ Finset.image (fun x : Fˣ => x ^ 5) Finset.univ) :
      (Finset.univ.filter fun x : Fˣ => x ^ 5 = b).card = 5 := by
    have hbRange : b ∈ Set.range fifthHom := by
      rw [Finset.mem_image] at hb
      obtain ⟨x, _, rfl⟩ := hb
      exact ⟨x, rfl⟩
    have hcard := MonoidHom.card_fiber_eq_of_mem_range fifthHom hbRange
      (show (1 : Fˣ) ∈ Set.range fifthHom from
        ⟨1, by simp [fifthHom]⟩)
    have hcard' :
        (Finset.univ.filter fun x : Fˣ => x ^ 5 = b).card =
          (Finset.univ.filter fun x : Fˣ => x ^ 5 = 1).card := by
      simpa [fifthHom] using hcard
    calc
      _ = (Finset.univ.filter fun x : Fˣ => x ^ 5 = 1).card := hcard'
      _ = Fintype.card fifthHom.ker := by
        rw [← Fintype.card_coe]
        symm
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        simp [fifthHom, MonoidHom.mem_ker]
      _ = 5 := hcardKer
  have horth (u : Fˣ) :
      (∑ chi : X, chi.1 (u : F)) =
        if u ∈ H then (5 : Complex) else 0 := by
    by_cases hu : u ∈ H
    · rw [if_pos hu]
      have hchi (chi : X) : chi.1 (u : F) = 1 :=
        (MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp chi.2) u hu
      simp_rw [hchi]
      simp [hcardX]
    · rw [if_neg hu]
      have hnot :
          ¬ ∀ chi : MulChar F Complex, chi ∈ X → chi (u : F) = 1 := by
        intro hall
        have hu' : u ∈
            (MulChar.subgroupOrderIsoSubgroupMulChar F Complex).symm
              (OrderDual.toDual X) :=
          MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff.mpr hall
        apply hu
        simpa [X] using hu'
      push Not at hnot
      obtain ⟨chiZero, hchiZeroX, hchiZero⟩ := hnot
      let chiZeroX : X := ⟨chiZero, hchiZeroX⟩
      let characterSum : Complex := ∑ chi : X, chi.1 (u : F)
      have hperm := Equiv.sum_comp (Equiv.mulLeft chiZeroX)
        (fun chi : X => chi.1 (u : F))
      have hmul : chiZero (u : F) * characterSum = characterSum := by
        calc
          chiZero (u : F) * characterSum =
              ∑ chi : X, (chiZeroX * chi).1 (u : F) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro chi _
            change chiZero (u : F) * chi.1 (u : F) =
              (chiZero * chi.1) (u : F)
            rw [MulChar.mul_apply]
          _ = characterSum := hperm
      have hz : (chiZero (u : F) - 1) * characterSum = 0 := by
        rw [sub_mul, one_mul, hmul, sub_self]
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hchiZero)
  have hunitPower :
      (∑ u : Fˣ, psi ((u : F) ^ 5)) =
        ∑ h : H, (5 : Complex) * psi (h.1 : F) := by
    have hcomp := Finset.sum_comp (s := Finset.univ)
      (fun u : Fˣ => psi (u : F)) (fun x : Fˣ => x ^ 5)
    calc
      (∑ u : Fˣ, psi ((u : F) ^ 5)) =
          ∑ b ∈ Finset.image (fun x : Fˣ => x ^ 5) Finset.univ,
            (Finset.univ.filter fun x : Fˣ => x ^ 5 = b).card •
              psi (b : F) := hcomp
      _ = ∑ b ∈ Finset.image (fun x : Fˣ => x ^ 5) Finset.univ,
          (5 : Complex) * psi (b : F) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hfiber b hb]
        simp [nsmul_eq_mul]
      _ = ∑ h : H, (5 : Complex) * psi (h.1 : F) := by
        apply Finset.sum_subtype
        intro b
        simp [H, fifthHom, MonoidHom.mem_range]
  have hcharacters :
      (∑ chi : X, gaussSum chi.1 psi) =
        ∑ h : H, (5 : Complex) * psi (h.1 : F) := by
    calc
      (∑ chi : X, gaussSum chi.1 psi) =
          ∑ x : F, (∑ chi : X, chi.1 x) * psi x := by
        simp only [gaussSum, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ u : Fˣ,
          (∑ chi : X, chi.1 (u : F)) * psi (u : F) := by
        rw [Fintype.sum_eq_add_sum_compl 0]
        simp only [MulChar.map_zero, Finset.sum_const_zero, zero_mul, zero_add]
        calc
          ∑ x ∈ ({0} : Finset F)ᶜ, (∑ chi : X, chi.1 x) * psi x =
              ∑ x : {x : F // x ≠ 0},
                (∑ chi : X, chi.1 x.1) * psi x.1 := by
            apply Finset.sum_subtype
            intro x
            simp
          _ = _ := by
            symm
            exact Fintype.sum_equiv unitsEquivNeZero
              (fun u : Fˣ =>
                (∑ chi : X, chi.1 (u : F)) * psi (u : F))
              (fun x : {x : F // x ≠ 0} =>
                (∑ chi : X, chi.1 x.1) * psi x.1)
              (fun _ => rfl)
      _ = ∑ u : Fˣ,
          if u ∈ H then (5 : Complex) * psi (u : F) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [horth]
        split_ifs <;> simp
      _ = ∑ h : H, (5 : Complex) * psi (h.1 : F) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_subtype
        intro u
        simp
  have hfieldUnits :
      (∑ x : F, psi (x ^ 5)) = 1 + ∑ u : Fˣ, psi ((u : F) ^ 5) := by
    rw [Fintype.sum_eq_add_sum_compl 0]
    simp only [zero_pow (by norm_num : 5 ≠ 0), AddChar.map_zero_eq_one]
    congr 1
    calc
      ∑ x ∈ ({0} : Finset F)ᶜ, psi (x ^ 5) =
          ∑ x : {x : F // x ≠ 0}, psi (x.1 ^ 5) := by
        apply Finset.sum_subtype
        intro x
        simp
      _ = ∑ u : Fˣ, psi ((u : F) ^ 5) := by
        symm
        exact Fintype.sum_equiv unitsEquivNeZero
          (fun u : Fˣ => psi ((u : F) ^ 5))
          (fun x : {x : F // x ≠ 0} => psi (x.1 ^ 5))
          (fun _ => rfl)
  have hdecomp :
      (∑ x : F, psi (x ^ 5)) =
        1 + ∑ chi : X, gaussSum chi.1 psi := by
    rw [hfieldUnits, hunitPower, hcharacters]
  have hpsiNe : psi ≠ 1 := by
    simpa using hpsi (show (1 : F) ≠ 0 from one_ne_zero)
  have honeMem : (1 : MulChar F Complex) ∈ X := by
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    intro u _
    exact MulChar.one_apply u.isUnit
  let oneX : X := ⟨1, honeMem⟩
  have htrivial : gaussSum oneX.1 psi = -1 := by
    exact gaussSum_one_left hpsiNe
  have hremove :
      (∑ x : F, psi (x ^ 5)) =
        ∑ chi ∈ ({oneX} : Finset X)ᶜ, gaussSum chi.1 psi := by
    rw [hdecomp, Fintype.sum_eq_add_sum_compl oneX, htrivial]
    ring
  rw [hremove]
  calc
    ‖∑ chi ∈ ({oneX} : Finset X)ᶜ, gaussSum chi.1 psi‖ ≤
        ∑ chi ∈ ({oneX} : Finset X)ᶜ, ‖gaussSum chi.1 psi‖ :=
      norm_sum_le _ _
    _ = ∑ _chi ∈ ({oneX} : Finset X)ᶜ,
        Real.sqrt (Fintype.card F) := by
      apply Finset.sum_congr rfl
      intro chi hchi
      apply norm_gaussSum_eq_sqrt_card
      · intro hchiOne
        have hchiEq : chi = oneX := Subtype.ext hchiOne
        simp [hchiEq] at hchi
      · exact hpsi
    _ = 4 * Real.sqrt (Fintype.card F) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_compl, Finset.card_singleton, hcardX]
      norm_num

/-- The prime-field fifth-power sum satisfies the four-square-root estimate
when five divides `p-1`. -/
theorem completePowerSum_fifth_prime_le_four_sqrt {p a : Nat} [NeZero p]
    (hp : p.Prime) (hFive : 5 ∣ p - 1) (ha : a.Coprime p) :
    ‖completePowerSum 5 ((a : Nat) : ZMod p)‖ ≤
      4 * Real.sqrt p := by
  letI : Fact p.Prime := ⟨hp⟩
  let psi : AddChar (ZMod p) Complex :=
    ZMod.stdAddChar.mulShift ((a : Nat) : ZMod p)
  have haZero : ((a : Nat) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp ha.symm
  have hpsiNe : psi ≠ 1 := (ZMod.isPrimitive_stdAddChar p) haZero
  have hpsi : psi.IsPrimitive := AddChar.IsPrimitive.of_ne_one hpsiNe
  have hFive' : 5 ∣ Fintype.card (ZMod p) - 1 := by
    simpa using hFive
  simpa only [completePowerSum, powerSum, psi, AddChar.mulShift_apply,
    ZMod.card] using fifthPower_sum_bound (F := ZMod p) hFive' hpsi

end Waring.Analytic
