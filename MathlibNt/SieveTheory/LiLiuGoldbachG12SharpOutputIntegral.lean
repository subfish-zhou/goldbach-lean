import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorAssemblyTools
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpMassIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalHighNormalized

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open G12AuthorOutput
namespace G12SharpOutput

/-- The complete original product-prime count, after paying the entire boundary,
the whole safe grid, cutoff slice, and genuine low/high weighted main mass. -/
theorem original_total_integral (τ : ℝ) (hτ : 0 < τ) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 2/15 → ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
      (goldbachG12SharpIntegralConstant+τ)*
        (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  let B := goldbachG12SharpIntegralConstant
  obtain ⟨t,ht,_htu,hpay⟩ := choose_loss B τ hτ
  obtain ⟨ρ,hρ,hρu,hboundary⟩ := admitted_boundary_mesh t ht
  obtain ⟨H,hH,hhigh⟩ := G12FineGrid.original_total_high_normalized t ht
  obtain ⟨M,_,hmass⟩ := g12Sharp_authorLowHigh_integral_budget t ht
  intro ε he heu
  obtain ⟨D,_,hbd⟩ := hboundary ε he heu
  obtain ⟨S,_,hsafe⟩ := G12SafeGridBudget.safe_union_normalized t t ht ht ε he
    (by linarith : ε ≤ 1) ρ hρ hρu
  refine ⟨max H (max M (max D S)),by omega,?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := hhigh N (by omega) hEven ρ hρ ε
  have hs := hsafe N (by omega) hEven
  have hb : G12LowHighOutput.outputCount N
      ((G12FineGrid.indices ρ N).biUnion (G12FineGrid.boundaryCell ρ N ε)) ≤
      t*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := hbd N (by omega) hEven
  rw [← G12SafeGridBudget.safe_union_sum hρ hN1 ε] at hp
  let Lm := goldbachG12AuthorLowMotherMass N ε
  let Hm := G12ClippedWindow.highMass N ε
  let Sm := ∑ p ∈ G12SafeGridBudget.safeUnion ρ N ε, goldbachG12NormalizedCoefficient N p.1*
    (goldbachG11AuthorWeight (Real.log p.2/Real.log N)+t)
  have hw : Sm ≤ (1+t)*Lm := safe_authorMass_le hN4 ρ ε ht.le
  have hh : 0 ≤ Hm := highMass_nonneg N ε
  have hmix : (8+t/2)*400*Hm+400*Sm ≤ (1+t)*400*(Lm+8*Hm) := by
    nlinarith only [hw,mul_nonneg ht.le hh]
  have hi : Real.log (N : ℝ)/(N : ℝ)*(400*(Lm+8*Hm)) ≤ B+t := by
    simpa only [mul_assoc] using hmass N (by omega) ε
  have hc : (8+t/2)*400*Hm*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
      400*Sm*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) ≤
      (1+t)*(B+t)*G12BandOutput.HN N := by
    calc
      _ = ((8+t/2)*400*Hm+400*Sm)*(SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by ring
      _ ≤ ((1+t)*400*(Lm+8*Hm))*(SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hmix (div_nonneg (SingularSeries.liuSingularSeries_pos N).le hl.le)
      _ = (1+t)*(Real.log (N : ℝ)/(N : ℝ)*(400*(Lm+8*Hm)))*G12BandOutput.HN N := by
        unfold G12BandOutput.HN
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by linarith))
        (G12BandOutput.HN_nonneg N)
  have hc' := mul_le_mul_of_nonneg_right hpay (G12BandOutput.HN_nonneg N)
  dsimp only [Hm,Sm,G12BandOutput.HN,B] at hc hc'
  nlinarith only [hp,hs,hb,hc,hc']

end G12SharpOutput
