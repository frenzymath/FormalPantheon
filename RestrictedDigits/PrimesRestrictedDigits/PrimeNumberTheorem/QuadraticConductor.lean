import PrimesRestrictedDigits.PrimeNumberTheorem.DecimalSmooth

/-!
# Quadratic conductors at decimal-smooth levels

This file proves the finite conductor classification. The set `{1, 4, 5, 8, 20, 40}` is a
derived corollary of the primitive local classification; it is not printed verbatim in the
source.

Source architecture: `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 9.2, Lemma 9.3, and the prime-power
classification on pp. 283--284, with the official p. 284 erratum applied.
-/

open MulChar

namespace PrimesRestrictedDigits

open DirichletCharacter

/-- Cardinality of the kernel of reduction between unit groups. -/
theorem card_ker_unitsMap_mul_totient {q d : Nat}
    [NeZero q] [NeZero d] (hd : d ∣ q) :
    Nat.card (ZMod.unitsMap hd).ker * d.totient = q.totient := by
  let f := ZMod.unitsMap hd
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker,
    f.range_eq_top_of_surjective (ZMod.unitsMap_surjective hd),
    Subgroup.card_top] at hcard
  simpa only [f, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient] using hcard

/-- No character at twice an odd level is primitive at the doubled level. -/
theorem factorsThrough_two_mul_of_odd {d : Nat} [NeZero d]
    (hd : Odd d) (chi : DirichletCharacter Complex (2 * d)) :
    chi.FactorsThrough d := by
  letI : NeZero (2 * d) := inferInstance
  have hdvd : d ∣ 2 * d := dvd_mul_left d 2
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd]
  have hsurj := ZMod.unitsMap_surjective hdvd
  have hcard : Fintype.card (ZMod d)ˣ =
      Fintype.card (ZMod (2 * d))ˣ := by
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
      Nat.totient_two_mul_of_odd hd]
  have hinj : Function.Injective (ZMod.unitsMap hdvd) :=
    ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨hsurj, hcard.symm⟩).1
  have hker : (ZMod.unitsMap hdvd).ker = ⊥ :=
    (ZMod.unitsMap hdvd).ker_eq_bot_iff.mpr hinj
  rw [hker]
  exact bot_le

/-- A quadratic character at `5 * d`, with `5 ∣ d`, factors through `d`. -/
theorem factorsThrough_five_mul_of_quadratic {d : Nat} [NeZero d]
    (h5 : 5 ∣ d) (chi : DirichletCharacter Complex (5 * d))
    (hchi : chi.IsQuadratic) : chi.FactorsThrough d := by
  letI : NeZero (5 * d) := inferInstance
  have hd : d ∣ 5 * d := dvd_mul_left d 5
  let f := ZMod.unitsMap hd
  have hcard : Nat.card f.ker = 5 := by
    apply Nat.mul_right_cancel (Nat.totient_pos.mpr (NeZero.pos d))
    rw [card_ker_unitsMap_mul_totient hd,
      Nat.totient_mul_of_prime_of_dvd Nat.prime_five h5]
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro x hx
  rw [MonoidHom.mem_ker]
  let xk : f.ker := ⟨x, hx⟩
  have hcard' : Fintype.card f.ker = 5 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hxk5 : xk ^ 5 = 1 := by
    have hxk := pow_card_eq_one (x := xk)
    simpa only [hcard'] using hxk
  have hx5 : x ^ 5 = 1 := congrArg Subtype.val hxk5
  let y := chi.toUnitHom x
  have hy5 : y ^ 5 = 1 := by
    dsimp only [y]
    rw [← map_pow, hx5, map_one]
  have hy2 : y ^ 2 = 1 := by
    apply Units.ext
    simp only [y, Units.val_pow_eq_pow_val, Units.val_one]
    have hv := DFunLike.congr_fun hchi.sq_eq_one (x : ZMod (5 * d))
    rw [MulChar.pow_apply' chi two_ne_zero,
      MulChar.one_apply x.isUnit] at hv
    simpa only [MulChar.coe_toUnitHom] using hv
  have hy4 : y ^ 4 = 1 := by
    calc
      y ^ 4 = y ^ (2 * 2) := by norm_num
      _ = (y ^ 2) ^ 2 := pow_mul y 2 2
      _ = 1 := by rw [hy2, one_pow]
  change y = 1
  calc
    y = 1 * y := by simp
    _ = y ^ 4 * y := by rw [hy4]
    _ = y ^ 5 := by
      simpa only [Nat.reduceAdd] using (pow_succ y 4).symm
    _ = 1 := hy5

/-- A quadratic character at `2 * d`, with `8 ∣ d`, factors through `d`. -/
theorem factorsThrough_two_mul_of_eight_dvd {d : Nat} [NeZero d]
    (h8 : 8 ∣ d) (chi : DirichletCharacter Complex (2 * d))
    (hchi : chi.IsQuadratic) : chi.FactorsThrough d := by
  obtain ⟨m, rfl⟩ := h8
  letI : NeZero m :=
    ⟨fun hm ↦ NeZero.ne (8 * m) (by simp [hm])⟩
  letI : NeZero (2 * (8 * m)) := inferInstance
  have hd : 8 * m ∣ 2 * (8 * m) := dvd_mul_left (8 * m) 2
  let f := ZMod.unitsMap hd
  have heven : _root_.Even (8 * m) := ⟨4 * m, by ring⟩
  have hcard : Nat.card f.ker = 2 := by
    apply Nat.mul_right_cancel
      (Nat.totient_pos.mpr (NeZero.pos (8 * m)))
    rw [card_ker_unitsMap_mul_totient hd,
      Nat.totient_two_mul_of_even heven]
  let uNat := 1 + 8 * m
  let vNat := 1 + 4 * m
  have hu2 : Nat.Coprime uNat 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨4 * m, by simp only [uNat]; ring⟩
  have hv2 : Nat.Coprime vNat 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨2 * m, by simp only [vNat]; ring⟩
  have hum : Nat.Coprime uNat m := by
    simp only [uNat]
    simpa only [mul_comm] using
      (Nat.coprime_add_mul_left_left 1 m 8).2 (by simp)
  have hvm : Nat.Coprime vNat m := by
    simp only [vNat]
    simpa only [mul_comm] using
      (Nat.coprime_add_mul_left_left 1 m 4).2 (by simp)
  have huq : Nat.Coprime uNat (2 * (8 * m)) := by
    have h := (Nat.Coprime.pow_right 4 hu2).mul_right hum
    norm_num only [pow_succ, pow_zero, mul_one] at h
    convert h using 1
    ring
  have hvq : Nat.Coprime vNat (2 * (8 * m)) := by
    have h := (Nat.Coprime.pow_right 4 hv2).mul_right hvm
    norm_num only [pow_succ, pow_zero, mul_one] at h
    convert h using 1
    ring
  let u : (ZMod (2 * (8 * m)))ˣ := ZMod.unitOfCoprime uNat huq
  let v : (ZMod (2 * (8 * m)))ˣ := ZMod.unitOfCoprime vNat hvq
  have hu_mem : u ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [ZMod.unitsMap_val]
    change ZMod.cast (uNat : ZMod (2 * (8 * m))) = 1
    rw [ZMod.cast_natCast hd, Nat.cast_add, Nat.cast_one]
    have hzero : ((8 * m : Nat) : ZMod (8 * m)) = 0 :=
      ZMod.natCast_self (8 * m)
    rw [hzero, add_zero]
  have hu_ne : u ≠ 1 := by
    intro h
    have hlt : uNat < 2 * (8 * m) := by
      simp only [uNat]
      nlinarith [NeZero.pos m]
    haveI : Fact (1 < 2 * (8 * m)) :=
      ⟨by nlinarith [NeZero.pos m]⟩
    have hv := congrArg
      (fun z : (ZMod (2 * (8 * m)))ˣ ↦ (z.val : ZMod _).val) h
    have huv : uNat = 1 := by
      simpa only [u, ZMod.coe_unitOfCoprime,
        ZMod.val_natCast_of_lt hlt, Units.val_one,
        ZMod.val_one] using hv
    simp only [uNat] at huv
    nlinarith [NeZero.pos m]
  have huv : v ^ 2 = u := by
    apply Units.ext
    simp only [v, u, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime]
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
    apply Nat.ModEq.symm
    have hle : uNat ≤ vNat ^ 2 := by
      simp only [uNat, vNat]
      nlinarith [sq_nonneg (4 * m : Int)]
    rw [Nat.modEq_iff_dvd' hle]
    use m
    rw [Nat.sub_eq_iff_eq_add hle]
    simp only [uNat, vNat]
    ring
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro x hx
  rw [MonoidHom.mem_ker]
  let xk : f.ker := ⟨x, hx⟩
  let uk : f.ker := ⟨u, hu_mem⟩
  have huk_ne : uk ≠ 1 := by
    intro h
    exact hu_ne (congrArg Subtype.val h)
  have hunique := (Nat.card_eq_two_iff' (1 : f.ker)).1 hcard
  by_cases hx_one : xk = 1
  · have hxval : x = 1 := congrArg Subtype.val hx_one
    rw [hxval, map_one]
  · have hxuk : xk = uk := hunique.unique hx_one huk_ne
    have hxu : x = u := congrArg Subtype.val hxuk
    rw [hxu, ← huv, map_pow]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    have hv := DFunLike.congr_fun hchi.sq_eq_one
      (v : ZMod (2 * (8 * m)))
    rw [MulChar.pow_apply' chi two_ne_zero,
      MulChar.one_apply v.isUnit] at hv
    simpa only [MulChar.coe_toUnitHom] using hv

/-- The complete list of possible primitive quadratic conductors supported on
the decimal primes. -/
def decimalQuadraticConductors : Finset Nat := {1, 4, 5, 8, 20, 40}

/-- A primitive quadratic character at a decimal-smooth level has one of the
six possible conductors. -/
theorem primitive_quadratic_conductor_mem {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q)
    (hprim : chi.IsPrimitive) (hquad : chi.IsQuadratic) :
    q ∈ decimalQuadraticConductors := by
  have hq0 := Nat.ne_zero_of_mem_factoredNumbers hq
  have hnot25 : ¬25 ∣ q := by
    intro h25
    obtain ⟨e, he⟩ := h25
    have he0 : 0 < e := by
      apply Nat.pos_of_ne_zero
      intro he0
      apply hq0
      simp [he, he0]
    have hlevel : q = 5 * (5 * e) := by omega
    clear he
    subst q
    letI : NeZero (5 * e) := ⟨by positivity⟩
    have hfac := factorsThrough_five_mul_of_quadratic
      (d := 5 * e) (dvd_mul_right 5 e) chi hquad
    have hle : chi.conductor ≤ 5 * e :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff chi).2 hfac)
    change chi.conductor = 5 * (5 * e) at hprim
    rw [hprim] at hle
    omega
  have hnot16 : ¬16 ∣ q := by
    intro h16
    obtain ⟨e, he⟩ := h16
    have he0 : 0 < e := by
      apply Nat.pos_of_ne_zero
      intro he0
      apply hq0
      simp [he, he0]
    have hlevel : q = 2 * (8 * e) := by omega
    clear he
    subst q
    letI : NeZero (8 * e) := ⟨by positivity⟩
    have hfac := factorsThrough_two_mul_of_eight_dvd
      (d := 8 * e) (dvd_mul_right 8 e) chi hquad
    have hle : chi.conductor ≤ 8 * e :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff chi).2 hfac)
    change chi.conductor = 2 * (8 * e) at hprim
    rw [hprim] at hle
    omega
  obtain ⟨a, b, hab⟩ :=
    (isDecimalSmooth_iff_exists_two_pow_mul_five_pow q).1 hq
  have hb : b ≤ 1 := by
    by_contra hb
    apply hnot25
    rw [hab]
    have hp : 5 ^ 2 ∣ 5 ^ b :=
      Nat.pow_dvd_pow 5 (by omega)
    norm_num at hp
    exact dvd_mul_of_dvd_right hp (2 ^ a)
  have ha : a ≤ 3 := by
    by_contra ha
    apply hnot16
    rw [hab]
    have hp : 2 ^ 4 ∣ 2 ^ a :=
      Nat.pow_dvd_pow 2 (by omega)
    norm_num at hp
    exact dvd_mul_of_dvd_left hp (5 ^ b)
  have ha1 : a ≠ 1 := by
    intro ha1
    subst a
    have hlevel : q = 2 * 5 ^ b := by simpa using hab
    clear hab
    subst q
    letI : NeZero (5 ^ b) := inferInstance
    have hodd : _root_.Odd (5 ^ b) :=
      (show _root_.Odd (5 : Nat) by decide).pow
    have hfac := factorsThrough_two_mul_of_odd hodd chi
    have hle : chi.conductor ≤ 5 ^ b :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff chi).2 hfac)
    change chi.conductor = 2 * 5 ^ b at hprim
    rw [hprim] at hle
    have hpos : 0 < 5 ^ b := by positivity
    omega
  have hacases : a = 0 ∨ a = 2 ∨ a = 3 := by omega
  have hbcases : b = 0 ∨ b = 1 := by omega
  rcases hacases with rfl | rfl | rfl <;>
    rcases hbcases with rfl | rfl <;>
    simp [hab, decimalQuadraticConductors]

/-- The conductor of any quadratic character at a decimal-smooth level is in
the finite primitive list. -/
theorem quadratic_conductor_mem {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q)
    (hquad : chi.IsQuadratic) :
    chi.conductor ∈ decimalQuadraticConductors := by
  letI : NeZero q := ⟨Nat.ne_zero_of_mem_factoredNumbers hq⟩
  exact primitive_quadratic_conductor_mem chi.primitiveCharacter
    (hq.conductor chi) chi.primitiveCharacter_isPrimitive
    (primitiveCharacter_isQuadratic chi hquad)

end PrimesRestrictedDigits
