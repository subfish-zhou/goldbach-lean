import HighIncrementGeometry

namespace HighIncrement
open Finset Real Wu2008DoubleSieve MixedSixth MixedEta Filter
open scoped Classical Topology
noncomputable section

def gainScalar (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ highCells δ n, gainWeight δ n i *
    truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)

/-- Exact classical debit is paid on the very same physical labels. -/
theorem E_lower {N n : ℕ} {δ : ℝ} (hN : 4 ≤ N) (hδ : 0 ≤ δ)
    (hm : 2*mesh n/truncatedSixthLowerAlpha ≤ reserve/2) :
    (∑ i ∈ highCells δ n, gainWeight δ n i *
      rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i)) ≤ E N n δ := by
  have hN1 : 1 < N := by omega
  have heq : truncatedSixthLowerNormalizedMain N δ 0 (selected N n (highCells δ n)) =
      ∑ k ∈ packing N n (highCells δ n), ∑ p ∈ pairBox N n k,
        wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p)*truncatedSixthLowerClassicalTheta N δ p := by
    unfold truncatedSixthLowerNormalizedMain selected
    simp only [mul_zero,sub_zero]
    exact sum_biUnion (physical_pairwise hN1 _)
  have hlab : ∀ k ∈ packing N n (highCells δ n),
      gainWeight δ n (outer k)*theta N n k δ +
        (∑ p ∈ pairBox N n k, wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p)*
          truncatedSixthLowerClassicalTheta N δ p) ≤
      highCoefficient δ n (outer k)*theta N n k δ := by
    intro k hk
    have hi := (packing_mem hk).1
    have hr := (actual_geometry hN1 hδ n).2.2.2.2.2.1 k hk
    have hlo := fine_lower_endpoints hN1 hk
    have hg := high_geometry hi
    have hb : (N:ℝ)^truncatedSixthLowerBeta ≤ (N:ℝ)^y N n k/truncatedSixthMassDelta N :=
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le)
        ((show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta]).trans hg.2.1)).trans hlo.2
    have ha : (N:ℝ)^truncatedSixthLowerAlpha ≤ (N:ℝ)^x N n k/truncatedSixthMassDelta N :=
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le) hg.1).trans hlo.1
    have hd : classicalMass N δ (pairBox N n k) ≤ theta N n k δ :=
      theta_dominates_classical hN hδ hr.1 ha hb
    have hcoef0 : 0 ≤ highCoefficient δ n (outer k)-gainWeight δ n (outer k) := by
      have hs := (source_bounds hδ hi).1
      have hc := (gainWeight_pos hδ hi).le
      have hl := log_nonneg (show 1 ≤ source δ n (outer k)-1 by linarith)
      unfold highCoefficient gainWeight source PositiveH.lowerCorrection at *
      dsimp at *
      linarith
    have hs : (∑ p ∈ pairBox N n k, wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p)*
        truncatedSixthLowerClassicalTheta N δ p) ≤
        (highCoefficient δ n (outer k)-gainWeight δ n (outer k))*classicalMass N δ (pairBox N n k) := by
      unfold classicalMass
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hpall := (actual_selected_geometry hN1 hδ n).2.1 (mem_biUnion.mpr ⟨k,hk,hp⟩)
      exact mul_le_mul_of_nonneg_right (by linarith [classical_coefficient_upper hN1 hδ hk hp hm])
        (truncatedSixthClosure_classical_theta_nonneg hN hδ hpall)
    have ht := hs.trans (mul_le_mul_of_nonneg_left hd hcoef0)
    nlinarith only [ht]
  have hall := sum_le_sum hlab
  rw [sum_add_distrib] at hall
  have hsum : (∑ k ∈ packing N n (highCells δ n), gainWeight δ n (outer k)*theta N n k δ) =
      ∑ i ∈ highCells δ n, gainWeight δ n i *
        rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
    rw [sum_packing]
    apply sum_congr rfl
    intro i _
    simp only [outer,MixedSixth.inner,x,y,Nat.unpair_pair,theta,rectangleTheta,mul_sum]
  have hmain : (∑ k ∈ packing N n (highCells δ n), highCoefficient δ n (outer k)*theta N n k δ) =
      highMain N n δ := rfl
  rw [hsum,hmain,← heq] at hall
  unfold E
  linarith only [hall]

/-- Sharp normalization of the paid increment, not of the unreduced highMain. -/
theorem gainScalar_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (n : ℕ)
    (hm : 2*mesh n/truncatedSixthLowerAlpha ≤ reserve/2) :
    ∀ᶠ N : ℕ in atTop, (gainScalar δ n-ε)*truncatedSixthMassScale N ≤ E N n δ := by
  let W := ∑ i ∈ highCells δ n, gainWeight δ n i
  have hW : 0 ≤ W := sum_nonneg (fun _ hi => (gainWeight_pos hδ hi).le)
  let e := ε/(W+1)
  have he : 0 < e := div_pos hε (by linarith)
  have herr : e*W ≤ ε := by
    have h := (div_le_iff₀ (show 0 < W+1 by linarith)).mpr
      (show ε*W ≤ ε*(W+1) by nlinarith)
    simpa only [e,div_mul_eq_mul_div] using h
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i ∈ highCells δ n,
      (truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)-e)*
        truncatedSixthMassScale N ≤ rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
    apply (eventually_all_finset _).mpr
    intro i hi
    have hg := high_geometry hi
    exact rectangle_theta_sharp hδ (truncatedSixthClosure_lo_lt_hi n (coarse i).1).le
      (truncatedSixthClosure_lo_lt_hi n (coarse i).2).le hg.1
      ((show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta]).trans hg.2.1) hg.2.2 he
  filter_upwards [hall,eventually_ge_atTop (4:ℕ)] with N hN hN4
  have hs := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hN i hi) (gainWeight_pos hδ hi).le)
  have heq : (∑ i ∈ highCells δ n, gainWeight δ n i *
      ((truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)-e)*
        truncatedSixthMassScale N)) = (gainScalar δ n-e*W)*truncatedSixthMassScale N := by
    unfold gainScalar W
    simp only [sub_mul,mul_sub,← mul_assoc]
    rw [sum_sub_distrib,← sum_mul,← sum_mul,← sum_mul]
    ring
  rw [heq] at hs
  exact (mul_le_mul_of_nonneg_right (by linarith only [herr])
    (truncatedSixthClosure_scale_nonneg hN4)).trans (hs.trans (E_lower hN4 hδ hm))

end
end HighIncrement
