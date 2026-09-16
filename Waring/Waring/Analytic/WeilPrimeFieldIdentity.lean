import Waring.Analytic.WeilExtensionSums

/-!
# The degree-one extension identity over the base field

A chosen degree-one finite-field extension is algebra-equivalent to its base
field.  Reindexing the extension sum through that equivalence specializes the
exact Euler power-sum identity to the original prime-field complete sum.
 -/

namespace Waring.Analytic

open scoped BigOperators

namespace Weil

/-- The base-field point-phase sum is the negative first power sum of the
Artin reciprocal roots. -/
theorem pointPhase_sum_eq_neg_artinRootSum
    {K : Type*} [Field K] [Fintype K]
    {p d : Nat} [Fact p.Prime] [CharP K p]
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) :
    (∑ x : K, character (pointPhase b x)) =
      -((artinLPolynomial character b d).reverse.roots.map
        fun z ↦ z ^ 1).sum := by
  let E := FiniteField.Extension K p 1
  letI : Fintype E := Fintype.ofFinite E
  let e : K ≃ₐ[K] E :=
    FiniteField.algEquivExtension K p 1 K (by simp)
  have hphase (x : K) :
      pointPhase ((algebraMap K E) ∘ b) (e x) =
        e (pointPhase b x) := by
    have hmap := pointPhase_map e.toRingEquiv.toRingHom b x
    rw [show e.toRingEquiv.toRingHom ∘ b =
        (algebraMap K E) ∘ b by
      funext i
      exact e.commutes (b i)] at hmap
    exact hmap.symm
  have hsummand (x : K) :
      character (pointPhase b x) =
        character
          (Algebra.trace K E
            (pointPhase ((algebraMap K E) ∘ b) (e x))) := by
    rw [hphase, Algebra.trace_eq_of_algEquiv e]
    simp only [Algebra.trace_self, LinearMap.id_coe, id_eq]
  have hreindex :
      (∑ x : K, character (pointPhase b x)) =
        ∑ y : E,
          character
            (Algebra.trace K E
              (pointPhase ((algebraMap K E) ∘ b) y)) := by
    calc
      (∑ x : K, character (pointPhase b x)) =
          ∑ x : K,
            character
              (Algebra.trace K E
                (pointPhase ((algebraMap K E) ∘ b) (e x))) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hsummand x
      _ = _ := by
        convert e.toEquiv.sum_comp
          (fun y : E ↦
            character
              (Algebra.trace K E
                (pointPhase ((algebraMap K E) ∘ b) y))) using 1
        apply Finset.sum_congr rfl
        intro x hx
        rfl
  rw [hreindex]
  exact extensionTraceSum_eq_neg_artinRootPowerSum
    K p 1 character hcharacter b hdpos hd5 hbtop hb hdcast

end Weil

end Waring.Analytic
