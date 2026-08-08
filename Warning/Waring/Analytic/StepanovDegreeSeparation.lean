import Waring.Analytic.StepanovParameters
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Nat.ModEq

/-!
# Degree separation in the pure-additive Stepanov construction

The auxiliary polynomial is evaluated at polynomials whose top degrees have
the form

`s + p ^ (2 * h + 5) * (d * i + p * k)`.

Here `s` is the degree of a coefficient polynomial and is strictly below
`p ^ (2 * h + 4)`, while `i < p`.  This file proves that these labels are
distinct.  It is the arithmetic input preventing cancellation of all top
terms in the evaluated auxiliary polynomial.
-/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

/-- The base separating a coefficient degree from the two auxiliary
indices. -/
def degreeBase (p h : Nat) : Nat :=
  p ^ (2 * h + 5)

/-- The natural-number degree label of one evaluated auxiliary monomial. -/
def degreeLabel (p h d s i k : Nat) : Nat :=
  s + degreeBase p h * (d * i + p * k)

/-- The coefficient cutoff is strictly below the base used in the degree
labels. -/
theorem S_lt_degreeBase {p h : Nat} (hp : 1 < p) :
    S p h < degreeBase p h := by
  rw [S, degreeBase]
  exact Nat.pow_lt_pow_right hp (by omega)

/-- Multiplication by `d` is injective modulo a prime `p` when
`0 < d < p`.  Consequently the mixed radix expression `d * i + p * k`
uniquely determines `i < p` and then `k`. -/
theorem mixedIndex_injective {p d i j k l : Nat} (hp : p.Prime)
    (hdpos : 0 < d) (hdp : d < p) (hi : i < p) (hj : j < p)
    (heq : d * i + p * k = d * j + p * l) :
    i = j ∧ k = l := by
  have hmod : d * i ≡ d * j [MOD p] := by
    have hwhole : d * i + p * k ≡ d * j + p * l [MOD p] := by
      rw [heq]
    simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using hwhole
  have hcop : p.Coprime d :=
    (hp.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt hdpos hdp)
  have hijMod : i ≡ j [MOD p] :=
    hmod.cancel_left_of_coprime hcop
  have hij : i = j := hijMod.eq_of_lt_of_lt hi hj
  subst j
  have hpk : p * k = p * l := Nat.add_left_cancel heq
  exact ⟨rfl, Nat.mul_left_cancel hp.pos hpk⟩

/-- Equality of two Stepanov top-degree labels forces equality of all three
indices.  The coefficient degrees need only satisfy the actual cutoff
`s,t < S p h`; the ordinary indices `k,l` are unrestricted. -/
theorem degreeLabel_injective {p h d s t i j k l : Nat} (hp : p.Prime)
    (hdpos : 0 < d) (hdp : d < p) (hs : s < S p h) (ht : t < S p h)
    (hi : i < p) (hj : j < p)
    (heq : degreeLabel p h d s i k = degreeLabel p h d t j l) :
    s = t ∧ i = j ∧ k = l := by
  have hpgt : 1 < p := hp.one_lt
  have hsBase : s < degreeBase p h := hs.trans (S_lt_degreeBase hpgt)
  have htBase : t < degreeBase p h := ht.trans (S_lt_degreeBase hpgt)
  have hmod : s ≡ t [MOD degreeBase p h] := by
    have hwhole :
        degreeLabel p h d s i k ≡ degreeLabel p h d t j l
          [MOD degreeBase p h] := by
      rw [heq]
    simpa [degreeLabel, Nat.ModEq, Nat.add_mod, Nat.mul_mod] using hwhole
  have hst : s = t := hmod.eq_of_lt_of_lt hsBase htBase
  subst t
  have hbasePos : 0 < degreeBase p h :=
    Nat.pow_pos hp.pos
  have hquotient :
      degreeBase p h * (d * i + p * k) =
        degreeBase p h * (d * j + p * l) := by
    exact Nat.add_left_cancel (by simpa only [degreeLabel] using heq)
  have hmixed : d * i + p * k = d * j + p * l :=
    Nat.mul_left_cancel hbasePos hquotient
  exact ⟨rfl, mixedIndex_injective hp hdpos hdp hi hj hmixed⟩

/-- Function-level version of `degreeLabel_injective`, convenient for a
finite family of nonzero coefficient polynomials. -/
theorem degreeLabel_family_injective {p h d : Nat} (hp : p.Prime)
    (hdpos : 0 < d) (hdp : d < p) {I : Type*}
    (s i k : I → Nat) (hs : ∀ a, s a < S p h)
    (hi : ∀ a, i a < p)
    (hcoordinates : Function.Injective fun a ↦ (s a, i a, k a)) :
    Function.Injective fun a ↦ degreeLabel p h d (s a) (i a) (k a) := by
  intro a b hab
  apply hcoordinates
  obtain ⟨hst, hij, hkl⟩ := degreeLabel_injective hp hdpos hdp
    (hs a) (hs b) (hi a) (hi b) hab
  simp only [Prod.mk.injEq]
  exact ⟨hst, hij, hkl⟩

/-- A finite sum of nonzero polynomials with distinct natural degrees cannot
vanish. -/
theorem polynomial_sum_ne_zero_of_natDegree_injOn
    {R I : Type*} [Semiring R] {u : Finset I} {F : I → R[X]}
    (hu : u.Nonempty) (hF : ∀ a ∈ u, F a ≠ 0)
    (hdegree : Set.InjOn (Polynomial.natDegree ∘ F) (↑u : Set I)) :
    ∑ a ∈ u, F a ≠ 0 := by
  classical
  have hpairwise :
      Set.Pairwise {a | a ∈ u ∧ F a ≠ 0}
        (fun a b ↦ Polynomial.degree (F a) ≠ Polynomial.degree (F b)) := by
    intro a ha b hb hab hdeg
    apply hab
    apply hdegree ha.1 hb.1
    rw [Function.comp_apply, Function.comp_apply]
    rw [Polynomial.degree_eq_natDegree ha.2,
      Polynomial.degree_eq_natDegree hb.2] at hdeg
    exact WithBot.coe_eq_coe.mp hdeg
  have hsum := Polynomial.degree_sum_eq_of_disjoint F u hpairwise
  intro hzero
  rw [hzero, Polynomial.degree_zero] at hsum
  obtain ⟨a, ha⟩ := hu
  have hale : Polynomial.degree (F a) ≤ u.sup fun b ↦ Polynomial.degree (F b) :=
    Finset.le_sup (f := fun b ↦ Polynomial.degree (F b)) ha
  have habot : Polynomial.degree (F a) = ⊥ :=
    bot_unique (hale.trans_eq hsum.symm)
  exact hF a ha (Polynomial.degree_eq_bot.mp habot)

/-- The degree-label arithmetic directly supplies the standard nonvanishing
step for a finite Stepanov auxiliary sum. -/
theorem polynomial_sum_ne_zero_of_degreeLabel
    {R I : Type*} [Semiring R] {u : Finset I} {F : I → R[X]}
    {p h d : Nat} (hp : p.Prime) (hdpos : 0 < d) (hdp : d < p)
    (s i k : I → Nat) (hu : u.Nonempty) (hF : ∀ a ∈ u, F a ≠ 0)
    (hs : ∀ a ∈ u, s a < S p h) (hi : ∀ a ∈ u, i a < p)
    (hdegree : ∀ a ∈ u,
      (F a).natDegree = degreeLabel p h d (s a) (i a) (k a))
    (hcoordinates :
      Set.InjOn (fun a ↦ (s a, i a, k a)) (↑u : Set I)) :
    ∑ a ∈ u, F a ≠ 0 := by
  apply polynomial_sum_ne_zero_of_natDegree_injOn hu hF
  intro a ha b hb hab
  apply hcoordinates ha hb
  have hlabels :
      degreeLabel p h d (s a) (i a) (k a) =
        degreeLabel p h d (s b) (i b) (k b) := by
    rw [← hdegree a ha, ← hdegree b hb]
    exact hab
  obtain ⟨hst, hij, hkl⟩ := degreeLabel_injective hp hdpos hdp
    (hs a ha) (hs b hb) (hi a ha) (hi b hb) hlabels
  simp only [Prod.mk.injEq]
  exact ⟨hst, hij, hkl⟩

end Stepanov

end Waring.Analytic
