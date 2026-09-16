import Waring.Analytic.BoundedPowerSums
import Waring.Analytic.FiniteFieldTraceInstances
import Waring.Analytic.StepanovExtensionSumBound
import Waring.Analytic.WeilExtensionSums

/-!
# Square-root radius of the Artin reciprocal roots

The exact extension-field power-sum identity converts the even-degree
Stepanov estimates into uniform bounds for the even power sums of the Artin
reciprocal roots.  The bounded-power-sum argument then puts every reciprocal
root in the disk of radius `sqrt p`.
 -/

namespace Waring.Analytic

open scoped BigOperators

namespace Weil

/-- Every reciprocal root of the prime-field Artin polynomial has norm at
most `sqrt p`. -/
theorem norm_artinLPolynomial_reverse_root_le_sqrt
    {p d : Nat} [Fact p.Prime] (hp : 1 < p)
    (hdpos : 0 < d) (hdp : d < p)
    (b : Fin 5 → ZMod p) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0) :
    ∀ z ∈ (artinLPolynomial ZMod.stdAddChar b d).reverse.roots,
      ‖z‖ ≤ Real.sqrt (p : Real) := by
  letI : NeZero p := ⟨by omega⟩
  have hcharacter :
      (ZMod.stdAddChar : AddChar (ZMod p) Complex) ≠ 1 := by
    intro htrivial
    have hprimitive := ZMod.isPrimitive_stdAddChar p
    have hshift := hprimitive (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, htrivial] at hshift
    exact hshift rfl
  have hdcast : (d : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hdpos hdp
  let roots := (artinLPolynomial ZMod.stdAddChar b d).reverse.roots
  have hbound : ∀ m, 3 ≤ m →
      ‖(roots.map fun z ↦ z ^ (2 * m)).sum‖ ≤
        (p * (d * (p - 1) * p + 1) : Nat) * (p : Real) ^ m := by
    intro m hm
    let h := m - 3
    have hmEq : h + 3 = m := by
      dsimp [h]
      omega
    letI : NeZero (2 * m) := ⟨by omega⟩
    letI : Fintype (FiniteField.Extension (ZMod p) p (2 * m)) :=
      Fintype.ofFinite _
    have hstep := Stepanov.norm_extension_pointPhase_sum_le
      hp hdpos hdp b hd5 hbtop hb h
    rw [hmEq] at hstep
    dsimp only at hstep
    have hexact :
        (∑ x : FiniteField.Extension (ZMod p) p (2 * m),
          ZMod.stdAddChar
            (Algebra.trace (ZMod p)
              (FiniteField.Extension (ZMod p) p (2 * m))
              (pointPhase
                ((algebraMap (ZMod p)
                  (FiniteField.Extension (ZMod p) p (2 * m))) ∘ b) x))) =
          -((artinLPolynomial ZMod.stdAddChar b d).reverse.roots.map
            fun z ↦ z ^ (2 * m)).sum := by
      have hcore := extensionTraceSum_eq_neg_artinRootPowerSum
        (ZMod p) p (2 * m) ZMod.stdAddChar hcharacter b
          hdpos hd5 hbtop hb hdcast
      calc
        (∑ x : FiniteField.Extension (ZMod p) p (2 * m),
          ZMod.stdAddChar
            (Algebra.trace (ZMod p)
              (FiniteField.Extension (ZMod p) p (2 * m))
              (pointPhase
                ((algebraMap (ZMod p)
                  (FiniteField.Extension (ZMod p) p (2 * m))) ∘ b) x))) =
            ∑ x : FiniteField.Extension (ZMod p) p (2 * m),
              ZMod.stdAddChar
                (FiniteFieldTraceInstances.baseTrace
                  (pointPhase
                    ((FiniteFieldTraceInstances.baseAlgebraMap
                      (p := p) (n := 2 * m)) ∘ b) x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact FiniteFieldTraceInstances.character_trace_pointPhase_eq_base
            ZMod.stdAddChar b x
        _ = -((artinLPolynomial ZMod.stdAddChar b d).reverse.roots.map
            fun z ↦ z ^ (2 * m)).sum := by
          simpa only [FiniteFieldTraceInstances.baseTrace,
            FiniteFieldTraceInstances.baseAlgebraMap] using hcore
    have hrootBound :
        ‖((artinLPolynomial ZMod.stdAddChar b d).reverse.roots.map
          fun z ↦ z ^ (2 * m)).sum‖ ≤
          (p * (d * (p - 1) * p + 1) * p ^ m : Nat) := by
      calc
        ‖((artinLPolynomial ZMod.stdAddChar b d).reverse.roots.map
            fun z ↦ z ^ (2 * m)).sum‖ =
            ‖-((artinLPolynomial ZMod.stdAddChar b d).reverse.roots.map
              fun z ↦ z ^ (2 * m)).sum‖ := (norm_neg _).symm
        _ = ‖∑ x : FiniteField.Extension (ZMod p) p (2 * m),
            ZMod.stdAddChar
              (Algebra.trace (ZMod p)
                (FiniteField.Extension (ZMod p) p (2 * m))
                (pointPhase
                  ((algebraMap (ZMod p)
                    (FiniteField.Extension (ZMod p) p (2 * m))) ∘ b) x))‖ :=
          congrArg norm hexact.symm
        _ ≤ _ := hstep
    simpa only [roots, norm_neg, Nat.cast_mul, Nat.cast_pow,
      mul_assoc] using hrootBound
  have hroot := norm_le_sqrt_of_bounded_even_multisetPowerSums roots
    (q := (p : Real))
    (C := (p * (d * (p - 1) * p + 1) : Nat))
    (by exact_mod_cast hp.le) 3 hbound
  exact hroot

end Weil

end Waring.Analytic
