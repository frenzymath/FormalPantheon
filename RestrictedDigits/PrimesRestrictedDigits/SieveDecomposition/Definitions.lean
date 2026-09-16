import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.PNat.Basic

/-!
# Finite sifted carriers and divisor dilation

This file implements the finite-set operations from Maynard's Section 6 while
distinguishing the source's strict threshold from the weak threshold required
by an exact least-prime-factor fiber.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--137.
-/

namespace PrimesRestrictedDigits

/-- Every prime divisor of `n` is strictly larger than `z`. -/
def strictRoughPredicate (z : Real) (n : Nat) : Prop :=
  ∀ p, p.Prime → p ∣ n → z < (p : Real)

/-- Every prime divisor of `n` is at least `z`. -/
def weakRoughPredicate (z : Real) (n : Nat) : Prop :=
  ∀ p, p.Prime → p ∣ n → z ≤ (p : Real)

@[simp] theorem strictRoughPredicate_zero {z : Real} :
    strictRoughPredicate z 0 ↔ z < 2 := by
  constructor
  · intro h
    exact h 2 Nat.prime_two (dvd_zero 2)
  · intro hz p hp _
    exact hz.trans_le (by exact_mod_cast hp.two_le)

@[simp] theorem weakRoughPredicate_zero {z : Real} :
    weakRoughPredicate z 0 ↔ z ≤ 2 := by
  constructor
  · intro h
    exact h 2 Nat.prime_two (dvd_zero 2)
  · intro hz p hp _
    exact hz.trans (by exact_mod_cast hp.two_le)

@[simp] theorem strictRoughPredicate_one (z : Real) :
    strictRoughPredicate z 1 := by
  intro p hp hpd
  exact (hp.not_dvd_one hpd).elim

@[simp] theorem weakRoughPredicate_one (z : Real) :
    weakRoughPredicate z 1 := by
  intro p hp hpd
  exact (hp.not_dvd_one hpd).elim

noncomputable def strictSiftedCarrier
    (C : Finset Nat) (z : Real) : Finset Nat := by
  classical
  exact C.filter (strictRoughPredicate z)

noncomputable def weakSiftedCarrier
    (C : Finset Nat) (z : Real) : Finset Nat := by
  classical
  exact C.filter (weakRoughPredicate z)

@[simp] theorem mem_strictSiftedCarrier
    {C : Finset Nat} {z : Real} {n : Nat} :
    n ∈ strictSiftedCarrier C z ↔
      n ∈ C ∧ strictRoughPredicate z n := by
  simp [strictSiftedCarrier]

@[simp] theorem mem_weakSiftedCarrier
    {C : Finset Nat} {z : Real} {n : Nat} :
    n ∈ weakSiftedCarrier C z ↔
      n ∈ C ∧ weakRoughPredicate z n := by
  simp [weakSiftedCarrier]

theorem strictSiftedCarrier_subset_weakSiftedCarrier
    (C : Finset Nat) (z : Real) :
    strictSiftedCarrier C z ⊆ weakSiftedCarrier C z := by
  intro n hn
  rw [mem_strictSiftedCarrier] at hn
  rw [mem_weakSiftedCarrier]
  exact ⟨hn.1, fun p hp hpd => (hn.2 p hp hpd).le⟩

theorem zero_mem_strictSiftedCarrier (C : Finset Nat) (z : Real) :
    0 ∈ strictSiftedCarrier C z ↔ 0 ∈ C ∧ z < 2 := by
  simp

theorem zero_mem_weakSiftedCarrier (C : Finset Nat) (z : Real) :
    0 ∈ weakSiftedCarrier C z ↔ 0 ∈ C ∧ z ≤ 2 := by
  simp

@[simp] theorem one_mem_strictSiftedCarrier (C : Finset Nat) (z : Real) :
    1 ∈ strictSiftedCarrier C z ↔ 1 ∈ C := by
  simp

@[simp] theorem one_mem_weakSiftedCarrier (C : Finset Nat) (z : Real) :
    1 ∈ weakSiftedCarrier C z ↔ 1 ∈ C := by
  simp

/-- The source dilation `C_d={n : n*d in C}`, with positivity bundled in
`d`. -/
noncomputable def sieveDilation
    (C : Finset Nat) (d : PNat) : Finset Nat :=
  C.preimage (fun n => n * (d : Nat))
    (mul_left_injective₀ (PNat.ne_zero d)).injOn

@[simp] theorem mem_sieveDilation
    {C : Finset Nat} {d : PNat} {n : Nat} :
    n ∈ sieveDilation C d ↔ n * (d : Nat) ∈ C := by
  simp [sieveDilation]

@[simp] theorem sieveDilation_one (C : Finset Nat) :
    sieveDilation C 1 = C := by
  ext n
  simp

theorem sieveDilation_mul (C : Finset Nat) (d e : PNat) :
    sieveDilation (sieveDilation C d) e = sieveDilation C (d * e) := by
  ext n
  simp [ mul_comm, mul_left_comm]

@[simp] theorem zero_mem_sieveDilation (C : Finset Nat) (d : PNat) :
    0 ∈ sieveDilation C d ↔ 0 ∈ C := by
  simp

@[simp] theorem one_mem_sieveDilation (C : Finset Nat) (d : PNat) :
    1 ∈ sieveDilation C d ↔ (d : Nat) ∈ C := by
  simp

theorem map_sieveDilation_eq_filter_dvd (C : Finset Nat) (d : PNat) :
    (sieveDilation C d).map
        ⟨fun n : Nat => n * (d : Nat),
          mul_left_injective₀ (PNat.ne_zero d)⟩ =
      C.filter fun n => (d : Nat) ∣ n := by
  ext n
  simp only [Finset.mem_map, mem_sieveDilation, Finset.mem_filter,
    dvd_iff_exists_eq_mul_left]
  constructor
  · rintro ⟨a, haC, han⟩
    exact ⟨han ▸ haC, ⟨a, han.symm⟩⟩
  · rintro ⟨hnC, a, hna⟩
    exact ⟨a, hna ▸ hnC, hna.symm⟩

theorem card_sieveDilation_eq_card_filter_dvd
    (C : Finset Nat) (d : PNat) :
    (sieveDilation C d).card =
      (C.filter fun n => (d : Nat) ∣ n).card := by
  rw [← map_sieveDilation_eq_filter_dvd]
  exact (Finset.card_map _).symm

/-- The ambient source set `B={0 <= n < X}`. -/
noncomputable def maynardAmbientCarrier (X : Real) : Finset Nat :=
  naturalLeftClosedRightOpenInterval 0 X

@[simp] theorem mem_maynardAmbientCarrier {X : Real} {n : Nat} :
    n ∈ maynardAmbientCarrier X ↔ (n : Real) < X := by
  simp [maynardAmbientCarrier, mem_naturalLeftClosedRightOpenInterval]

theorem sieveDilation_maynardAmbientCarrier (X : Real) (d : PNat) :
    sieveDilation (maynardAmbientCarrier X) d =
      maynardAmbientCarrier (X / (d : Real)) := by
  ext n
  simp only [mem_sieveDilation, mem_maynardAmbientCarrier, Nat.cast_mul]
  rw [lt_div_iff₀ (by positivity : (0 : Real) < d)]

/-- At a prime threshold, weak-but-not-strict elements form the whole
prime-multiple fiber over the weakly sifted dilation. -/
theorem weakSiftedCarrier_sdiff_strict_eq_primeFiber
    (C : Finset Nat) {q : Nat} (hq : q.Prime) :
    weakSiftedCarrier C (q : Real) \ strictSiftedCarrier C (q : Real) =
      (weakSiftedCarrier (sieveDilation C ⟨q, hq.pos⟩) (q : Real)).map
        ⟨fun m => m * q, mul_left_injective₀ hq.ne_zero⟩ := by
  classical
  ext n
  constructor
  · intro hn
    have hnDiff := Finset.mem_sdiff.mp hn
    have hnWeak := mem_weakSiftedCarrier.mp hnDiff.1
    have hnNotStrict : ¬strictRoughPredicate (q : Real) n := by
      intro hnStrict
      exact hnDiff.2 (mem_strictSiftedCarrier.mpr ⟨hnWeak.1, hnStrict⟩)
    simp only [strictRoughPredicate] at hnNotStrict
    push Not at hnNotStrict
    obtain ⟨p, hp, hpn, hpq⟩ := hnNotStrict
    have hqp : q ≤ p := by
      exact_mod_cast hnWeak.2 p hp hpn
    have hpqNat : p ≤ q := by exact_mod_cast hpq
    have hpEq : p = q := Nat.le_antisymm hpqNat hqp
    subst p
    have hdiv : q ∣ n := hpn
    apply Finset.mem_map.mpr
    refine ⟨n / q, ?_, Nat.div_mul_cancel hdiv⟩
    rw [mem_weakSiftedCarrier, mem_sieveDilation]
    refine ⟨?_, ?_⟩
    · simpa [Nat.div_mul_cancel hdiv] using hnWeak.1
    · intro r hr hrd
      apply hnWeak.2 r hr
      rw [← Nat.div_mul_cancel hdiv]
      exact dvd_mul_of_dvd_left hrd q
  · intro hn
    rcases Finset.mem_map.mp hn with ⟨m, hm, rfl⟩
    rw [Finset.mem_sdiff]
    rw [mem_weakSiftedCarrier] at hm
    rw [mem_sieveDilation] at hm
    refine ⟨mem_weakSiftedCarrier.mpr ⟨hm.1, ?_⟩, ?_⟩
    · intro r hr hrd
      rcases hr.dvd_mul.mp hrd with hrm | hrq
      · exact hm.2 r hr hrm
      · have hrEq : r = q :=
          (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
        subst r
        exact le_rfl
    · intro hstrict
      have hqStrict := (mem_strictSiftedCarrier.mp hstrict).2 q hq (by simp)
      exact (lt_irrefl (q : Real)) hqStrict

/-- Cardinal form of the exact weak-minus-strict prime fiber. -/
theorem weakSiftedCarrier_card_eq_strict_add_primeFiber
    (C : Finset Nat) {q : Nat} (hq : q.Prime) :
    (weakSiftedCarrier C (q : Real)).card =
      (strictSiftedCarrier C (q : Real)).card +
        (weakSiftedCarrier (sieveDilation C ⟨q, hq.pos⟩)
          (q : Real)).card := by
  have hsubset := strictSiftedCarrier_subset_weakSiftedCarrier C (q : Real)
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  rw [weakSiftedCarrier_sdiff_strict_eq_primeFiber C hq,
    Finset.card_map] at hcard
  omega

end PrimesRestrictedDigits
