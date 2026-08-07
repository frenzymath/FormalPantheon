import BoundedGaps.Maynard.MaynardCoprimeHarmonic

noncomputable section

/-!
# Prime adjunction for coprime harmonic sums

Adjoining a new prime to the coprimality modulus removes exactly the positive
multiples of that prime. Reindexing those multiples gives the finite
recurrence used in the specialized cumulative summation argument.
-/

namespace BoundedGaps.Maynard

theorem coprimeHarmonicSum_mul_prime
    {W p Q : ℕ} (hp : p.Prime) (hpW : Nat.Coprime p W) :
    coprimeHarmonicSum (W * p) Q =
      coprimeHarmonicSum W Q -
        (1 : ℝ) / p * coprimeHarmonicSum W (Q / p) := by
  classical
  let S := (Finset.Icc 1 Q).filter (Nat.Coprime · W)
  let T := (Finset.Icc 1 (Q / p)).filter (Nat.Coprime · W)
  let bad := S.filter (fun n => ¬Nat.Coprime n p)
  have hleft :
      (Finset.Icc 1 Q).filter (Nat.Coprime · (W * p)) =
        S.filter (Nat.Coprime · p) := by
    ext n
    simp only [S, Finset.mem_filter, Nat.coprime_mul_iff_right]
    tauto
  have hbad :
      (∑ n ∈ bad, (1 : ℝ) / n) =
        (1 : ℝ) / p * ∑ m ∈ T, (1 : ℝ) / m := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij'
      (fun n _ => n / p) (fun m _ => p * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnS := Finset.mem_filter.mp hnData.1
      have hnBounds := Finset.mem_Icc.mp hnS.1
      have hpdvd : p ∣ n := by
        by_contra hnot
        exact hnData.2 ((hp.coprime_iff_not_dvd.mpr hnot).symm)
      have hnPos : 0 < n := zero_lt_one.trans_le hnBounds.1
      have hquotPos : 0 < n / p :=
        Nat.div_pos (Nat.le_of_dvd hnPos hpdvd) hp.pos
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hquotPos, ?_⟩, ?_⟩
      · exact Nat.div_le_div_right hnBounds.2
      · exact Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hpdvd) hnS.2
    · intro m hm
      have hmData := Finset.mem_filter.mp hm
      have hmBounds := Finset.mem_Icc.mp hmData.1
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos
          (zero_lt_one.trans_le hmBounds.1), ?_⟩, hpW.mul_left hmData.2⟩
        have hmul : m * p ≤ Q :=
          (Nat.le_div_iff_mul_le hp.pos).mp hmBounds.2
        simpa [Nat.mul_comm] using hmul
      · intro hcop
        exact (hp.coprime_iff_not_dvd.mp hcop.symm)
          (Nat.dvd_mul_right p m)
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hpdvd : p ∣ n := by
        by_contra hnot
        exact hnData.2 ((hp.coprime_iff_not_dvd.mpr hnot).symm)
      exact Nat.mul_div_cancel' hpdvd
    · intro m hm
      exact Nat.mul_div_cancel_left m hp.pos
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnBounds := Finset.mem_Icc.mp
        (Finset.mem_filter.mp hnData.1).1
      have hpdvd : p ∣ n := by
        by_contra hnot
        exact hnData.2 ((hp.coprime_iff_not_dvd.mpr hnot).symm)
      have hquotPos : 0 < n / p :=
        Nat.div_pos (Nat.le_of_dvd
          (zero_lt_one.trans_le hnBounds.1) hpdvd) hp.pos
      have hprod : (n : ℝ) = (p : ℝ) * (n / p : ℕ) := by
        exact_mod_cast (Nat.mul_div_cancel' hpdvd).symm
      rw [hprod]
      field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (Nat.Coprime · p) (fun n => (1 : ℝ) / n)
  unfold coprimeHarmonicSum
  rw [hleft]
  change (∑ n ∈ S.filter (Nat.Coprime · p), (1 : ℝ) / n) = _
  change _ = (∑ n ∈ S, (1 : ℝ) / n) -
    (1 : ℝ) / p * ∑ m ∈ T, (1 : ℝ) / m
  rw [← hbad]
  change _ = (∑ n ∈ S, (1 : ℝ) / n) -
    ∑ n ∈ S.filter (fun n => ¬Nat.Coprime n p), (1 : ℝ) / n
  linarith

end BoundedGaps.Maynard
