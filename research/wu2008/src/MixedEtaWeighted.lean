import MixedEtaDebit

namespace MixedEta
open Finset Real Wu2008DoubleSieve MixedSixth Filter
open scoped Classical Topology
noncomputable section

def highScalar (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ highCells δ n, highCoefficient δ n i *
    truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)

def highMain (N n : ℕ) (δ : ℝ) : ℝ :=
  ∑ k ∈ packing N n (highCells δ n),
    (log (sourceS δ n k-1)+(1/10000)*log (2/(sourceS δ n k-1)))*theta N n k δ

/-- The actual fine-grid labels carry their original coarse coefficient, without dropping weights. -/
theorem highMain_eq (N n : ℕ) (δ : ℝ) :
    highMain N n δ = ∑ i ∈ highCells δ n, highCoefficient δ n i *
      rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  unfold highMain
  rw [sum_packing]
  apply sum_congr rfl
  intro i _
  simp only [sourceS,outer,MixedSixth.inner,x,y,Nat.unpair_pair,theta,highCoefficient,rectangleTheta,mul_sum]

/-- Every fixed symbolic coarse grid has the full weighted lower scalar.
Only the existing sharp rectangle limit is used; no numerical evaluation or chosen mesh. -/
theorem high_weighted_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (highScalar δ n-ε)*truncatedSixthMassScale N ≤ highMain N n δ := by
  let W := ∑ i ∈ highCells δ n, highCoefficient δ n i
  have hW : 0 ≤ W := sum_nonneg (fun _ hi => (highCoefficient_pos hδ hi).le)
  let e := ε/(W+1)
  have he : 0 < e := div_pos hε (by linarith)
  have herr : e*W ≤ ε := by
    have h := (div_le_iff₀ (show 0 < W+1 by linarith)).mpr
      (show ε*W ≤ ε*(W+1) by nlinarith)
    change ε/(W+1)*W ≤ ε
    simpa only [div_mul_eq_mul_div] using h
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i ∈ highCells δ n,
      (truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)-e)*
        truncatedSixthMassScale N ≤ rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
    apply (eventually_all_finset _).mpr
    intro i hi
    have hg := high_geometry hi
    apply rectangle_theta_sharp hδ
      (truncatedSixthClosure_lo_lt_hi n (coarse i).1).le
      (truncatedSixthClosure_lo_lt_hi n (coarse i).2).le hg.1 _ hg.2.2 he
    exact (show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta]).trans hg.2.1
  filter_upwards [hall,eventually_ge_atTop (4:ℕ)] with N hN hN4
  have hs := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hN i hi)
    (highCoefficient_pos hδ hi).le)
  rw [highMain_eq]
  have heq : (∑ i ∈ highCells δ n,
      highCoefficient δ n i*((truncatedSixthMassRectangleCoefficient δ
        (loX n i) (hiX n i) (loY n i) (hiY n i)-e)*truncatedSixthMassScale N)) =
      (highScalar δ n-e*W)*truncatedSixthMassScale N := by
    unfold highScalar W
    simp only [sub_mul,mul_sub,← mul_assoc]
    rw [sum_sub_distrib,← sum_mul,← sum_mul,← sum_mul]
    ring
  rw [heq] at hs
  exact (mul_le_mul_of_nonneg_right (by linarith only [herr])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hs

end
end MixedEta
