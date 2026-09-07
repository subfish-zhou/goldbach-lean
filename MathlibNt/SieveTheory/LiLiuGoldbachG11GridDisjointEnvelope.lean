import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorGridCount

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11GridIndex_eq_of_bounds {ρ t : ℝ} (hρ : 1 < ρ) {i : ℕ}
    (hi : ρ^i ≤ t) (hiu : t < ρ^(i+1)) : fouvryG9GridIndex ρ t = i := by
  have ht : 1 ≤ t := (one_le_pow₀ hρ.le).trans hi
  have hc := fouvryG9GridIndex_bounds hρ ht
  apply Nat.le_antisymm
  · by_contra h
    have hj : i+1 ≤ fouvryG9GridIndex ρ t := by omega
    have hp := pow_le_pow_right₀ hρ.le hj
    linarith [hc.1]
  · by_contra h
    have hj : fouvryG9GridIndex ρ t+1 ≤ i := by omega
    have hp := pow_le_pow_right₀ hρ.le hj
    linarith [hc.2]

/-- The half-open endpoints give a unique key even for added rectangle points. -/
theorem goldbachG11Grid_rectangle_key {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) {v : ℕ × ℕ}
    (hv : v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k) :
    goldbachG11GridKey ρ v = k := by
  obtain ⟨hm,hp⟩ := mem_product.mp hv
  have hmB := (mem_filter.mp hm).2
  have hpB := (goldbachG11GridShort_mem_iff hρ hρu hbig hk v.2).mp hp
  apply Prod.ext
  · exact goldbachG11GridIndex_eq_of_bounds hρ ((le_max_left _ _).trans hpB.1) hpB.2
  · exact goldbachG11GridIndex_eq_of_bounds hρ hmB.1 hmB.2.1

def goldbachG11ExpandedGridPairs (N : ℕ) (ε ρ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachG11GridUsed N ε ρ).biUnion fun k => goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k

/-- Forgetting grid keys loses no multiplicity: distinct boxes are disjoint. -/
theorem goldbachG11WeightedGridMass_eq_union {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ)) (h : ℝ → ℝ) :
    goldbachG11WeightedGridMass N ε ρ h =
      ∑ v ∈ goldbachG11ExpandedGridPairs N ε ρ,
        goldbachG11AllPrimeWeight N v*h (Real.log (v.2 : ℝ)/Real.log (N : ℝ)) := by
  unfold goldbachG11ExpandedGridPairs
  rw [sum_biUnion]
  · rfl
  · intro k hk l hl hkl
    apply disjoint_left.mpr
    intro v hv hv'
    exact hkl ((goldbachG11Grid_rectangle_key hρ hρu hbig hk hv).symm.trans
      (goldbachG11Grid_rectangle_key hρ hρu hbig hl hv'))

/-- The only geometric extensions are a multiplicative product endpoint rho^2*N
and a first/second-prime ordering collar p<rho*minFac(m). -/
theorem goldbachG11ExpandedGridPairs_data {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {v : ℕ × ℕ} (hv : v ∈ goldbachG11ExpandedGridPairs N ε ρ) :
    v.1 ∈ goldbachG11EffectiveProductSupport N ε ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (v.2 : ℝ) ∧
      (v.2 : ℝ) < ρ*v.1.minFac ∧ (v.1 : ℝ)*v.2 < ρ^2*N := by
  obtain ⟨k,hk,hv⟩ := mem_biUnion.mp hv
  obtain ⟨hm,hp⟩ := mem_product.mp hv
  obtain ⟨hmS,hmlo,hmhi,hmin⟩ := mem_filter.mp hm
  obtain ⟨hplo,hphi⟩ := (goldbachG11GridShort_mem_iff hρ hρu hbig hk v.2).mp hp
  have hρ0 : 0 < ρ := by linarith
  have hM : 0 < ρ^k.2 := pow_pos hρ0 _
  have hT : 0 < ρ^k.1 := pow_pos hρ0 _
  have hp0 : (0 : ℝ) < v.2 := hT.trans_le ((le_max_left _ _).trans hplo)
  obtain ⟨m₀,p₀,_hm₀,hp₀,ht₀,_ht₁,hm₀,_hm₁⟩ := goldbachG11GridUsed_witness hρ hk
  have hprod := (mem_goldbachG11ProductFirstPrimeFiber_iff.mp hp₀).2.2.2.2.2.1
  have hprodR : (p₀ : ℝ)*m₀ < N := by exact_mod_cast hprod
  have hMT := mul_le_mul hm₀ ht₀ hT.le (Nat.cast_nonneg m₀)
  have hMTN : ρ^k.2*ρ^k.1 < N := by nlinarith
  rw [pow_succ] at hmhi hphi
  refine ⟨hmS,(le_max_right _ _).trans hplo,?_,?_⟩
  · have hh := hphi.trans_le (mul_le_mul_of_nonneg_right hmin hρ0.le)
    simpa only [mul_comm] using hh
  · calc
      _ < (ρ^k.2*ρ)*(ρ^k.1*ρ) := mul_lt_mul hmhi hphi.le hp0 (mul_pos hM hρ0).le
      _ = ρ^2*(ρ^k.2*ρ^k.1) := by ring
      _ < _ := mul_lt_mul_of_pos_left hMTN (sq_pos_of_pos hρ0)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig