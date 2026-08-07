import BoundedGaps.Maynard.MaynardS1NontrivialMobius

noncomputable section

/-!
# Fixed boxes for S1 cross variables

Dependent gcd-divisor supports are identified with filters of one global
positive radius box.
-/

namespace BoundedGaps.Maynard

local instance crossBoxesDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def crossMoebiusTupleBox (H : Finset ℕ) (R : ℕ) :
    Finset (∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :=
  (offDiagonalPairs H).pi (fun _ => Finset.Icc 1 R)

def CrossTupleDivides
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (d e : H → ℕ) : Prop :=
  ∀ (ab : H × H) (hab : ab ∈ offDiagonalPairs H),
    s ab hab ∣ d ab.1 ∧ s ab hab ∣ e ab.2

theorem filter_crossMoebiusTupleBox_eq_support
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    (crossMoebiusTupleBox H R).filter
        (fun s => CrossTupleDivides H s d e) =
      crossMoebiusTupleSupport H d e := by
  classical
  ext s
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hsBox, hs⟩
    exact (mem_crossMoebiusTupleSupport_iff hd s).mpr hs
  · intro hsSupport
    have hs := (mem_crossMoebiusTupleSupport_iff hd s).mp hsSupport
    refine ⟨?_, hs⟩
    rw [crossMoebiusTupleBox, Finset.mem_pi]
    intro ab hab
    apply Finset.mem_Icc.mpr
    have hdPos : 0 < d ab.1 :=
      Nat.pos_of_ne_zero (hd.coordinate_squarefree ab.1).ne_zero
    have hsPos : 0 < s ab hab := Nat.pos_of_dvd_of_pos (hs ab hab).1 hdPos
    have hdProdPos : 0 < divisorTupleProduct H d :=
      Nat.pos_of_ne_zero hd.2.2.ne_zero
    have hdLe : d ab.1 ≤ divisorTupleProduct H d :=
      Nat.le_of_dvd hdProdPos (divisorTupleCoordinate_dvd_product d ab.1)
    have hsLe : s ab hab ≤ d ab.1 := Nat.le_of_dvd hdPos (hs ab hab).1
    exact ⟨hsPos, (hsLe.trans hdLe).trans hd.1.le⟩

theorem filter_crossMoebiusTupleBox_ne_one_eq_erase_support
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    (crossMoebiusTupleBox H R).filter
        (fun s => s ≠ oneCrossMoebiusTuple H ∧ CrossTupleDivides H s d e) =
      (crossMoebiusTupleSupport H d e).erase (oneCrossMoebiusTuple H) := by
  classical
  ext s
  rw [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hsBox, hsNe, hsDiv⟩
    exact ⟨hsNe, (mem_crossMoebiusTupleSupport_iff hd s).mpr hsDiv⟩
  · rintro ⟨hsNe, hsSupport⟩
    have hfiltered : s ∈ (crossMoebiusTupleBox H R).filter
        (fun t => CrossTupleDivides H t d e) := by
      rw [filter_crossMoebiusTupleBox_eq_support hd]
      exact hsSupport
    exact ⟨(Finset.mem_filter.mp hfiltered).1, hsNe,
      (Finset.mem_filter.mp hfiltered).2⟩

end BoundedGaps.Maynard
